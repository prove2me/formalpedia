-- Prove2me | Theorems.Thm_GraphConvSubgrad_StatConc_theorem_4_1
-- name    : GraphConvSubgrad.StatConc.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:18.557656+00:00
-- url     : https://prove2.me/theorems/dd33a967-1aae-40d7-95c4-03c5c6ee6a13
-- title:
--   Theorem 4.1, pp. 11–12 — stability of Bregman-regularized ERM, (4.1)–(4.3), read with A∗ = prox^Φ_{φ/ρ̄}(y), A(S) = prox^Φ_{φ_S/ρ̄}(y)
-- statement:
--   Assume (A1)–(A3) for $\Phi$, $r$, $f$, $L$ with constants $\rho,\alpha,\sigma$. Fix a sample size $m\ge1$, a point $y\in\operatorname{int}(\operatorname{dom}\Phi)$ and $\bar\rho>\max(\rho,0)$. For a sample $S=(z_1,\dots,z_m)$ write $S^i=(z_1,\dots,z_{i-1},z_i',z_{i+1},\dots,z_m)$, and let
--   $$\mathcal A^*=\operatorname{prox}^\Phi_{\varphi/\bar\rho}(y),\qquad \mathcal A(S)=\operatorname{prox}^\Phi_{\varphi_S/\bar\rho}(y)$$
--   be the minimizers of $\varphi(x)+\bar\rho D_\Phi(x,y)$ and of $\varphi_S(x)+\bar\rho D_\Phi(x,y)$. Then:
--
--   1. (4.1) for every $S$, $i$ and $z_i'$ such that $z_1,\dots,z_m,z_i'$ all satisfy (A2),
--   $$\sqrt{D^{\mathrm{sym}}_\Phi(\mathcal A(S),\mathcal A(S^i))}\le\frac{L(z_i)+L(z_i')}{(\bar\rho-\rho)m};$$
--   2. (4.2) with $S\sim P^m$,
--   $$\mathbb E_S\big[D_\Phi(\mathcal A(S),\mathcal A^*)\big]\le\frac{2\sigma^2}{(\bar\rho-\rho)^2m};$$
--   3. (4.3) $\varphi^\Phi_{1/\bar\rho}(y)-(\varphi_S)^\Phi_{1/\bar\rho}(y)$ is integrable in $S$ and
--   $$0\le\mathbb E_S\big[\varphi^\Phi_{1/\bar\rho}(y)-(\varphi_S)^\Phi_{1/\bar\rho}(y)\big]\le\frac{2\sigma^2}{(\bar\rho-\rho)m}.$$
--
--   The first estimate is the stability of the regularized empirical minimizer under replacement of one sample, the second its expected distance from the population minimizer; both feed the concentration argument of Theorem 4.4.
--
--   **Formalization Note** The page defines $\mathcal A^*$ and $\mathcal A(S)$ with $y$ both as the fixed centre and as the minimization variable; the proof (p. 12) minimizes $\hat\varphi(x)=\varphi(x)+\bar\rho D_\Phi(x,y)$, so they are the proximal points at $y$, which is what is stated. (4.1) is stated for every pair of points of the two proximal sets and requires (A2) at the $m+1$ sample points (a full-measure condition; the paper takes $z_i'$ arbitrary, while (A2) holds only almost surely). In (4.2), $\mathcal A$ is any a.e. strongly measurable selection of the empirical proximal set (the paper treats $\mathcal A(S)$ as a random variable) and the expectation is a lower Lebesgue integral of the nonnegative divergence; the bound holds for every point $\mathcal A^*$ of the population proximal set. $0<\bar\rho$ is added: $\bar\rho=1/\lambda$ in Theorem 3.1.
-- source:
--   Davis, Drusvyatskiy, Graphical Convergence of Subgradients in Nonconvex Optimization and Learning, arXiv:1810.07590v2, pp. 11–12, Theorem 4.1, (4.1)–(4.3)

import Mathlib
import Definitions.Def_GraphConvSubgrad_StatConc_Setting

namespace GraphConvSubgrad.StatConc

open MeasureTheory

/-- Theorem 4.1 (Stability of regularized ERM), pp. 11–12, read with `A* = prox^Φ_{φ/ρ̄}(y)` and
`A(S) = prox^Φ_{φ_S/ρ̄}(y)` as in its proof. Under (A1)–(A3), for `y ∈ int (dom Φ)` and
`0 < ρ̄`, `ρ < ρ̄`:
(4.1) `√(D^sym_Φ(A(S), A(Sⁱ))) ≤ (L(zᵢ) + L(z'ᵢ)) / ((ρ̄ − ρ) m)` whenever all sample points
satisfy (A2);
(4.2) `E_S[D_Φ(A(S), A*)] ≤ 2σ² / ((ρ̄ − ρ)² m)` for any a.e. selection `A` of the empirical prox;
(4.3) `0 ≤ E_S[φ^Φ_{1/ρ̄}(y) − (φ_S)^Φ_{1/ρ̄}(y)] ≤ 2σ² / ((ρ̄ − ρ) m)`, the integrand integrable. -/
theorem theorem_4_1 {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Φ r : ExtFn E) (f : E → Ω → ℝ) (L : Ω → ℝ) (ρ α σ : ℝ)
    (hA : Assumptions P Φ r f L ρ α σ)
    (m : ℕ) (hm : 0 < m) (y : E) (hy : y ∈ interior Φ.dom)
    (rhoBar : ℝ) (hρ : ρ < rhoBar) (hρ0 : 0 < rhoBar) :
    -- (4.1)
    (∀ (S : Fin m → Ω) (i : Fin m) (z' : Ω),
      (∀ j, GoodSample Φ r f ρ (S j)) → GoodSample Φ r f ρ z' →
      ∀ a ∈ proxSet Φ (empRisk r f S) rhoBar y,
      ∀ b ∈ proxSet Φ (empRisk r f (Function.update S i z')) rhoBar y,
        Real.sqrt (bregmanSym Φ a b) ≤ (L (S i) + L z') / ((rhoBar - ρ) * m)) ∧
    -- (4.2)
    (∀ A : (Fin m → Ω) → E, AEStronglyMeasurable A (Measure.pi fun _ : Fin m => P) →
      (∀ᵐ S ∂(Measure.pi fun _ : Fin m => P), A S ∈ proxSet Φ (empRisk r f S) rhoBar y) →
      ∀ b ∈ proxSet Φ (popRisk P r f) rhoBar y,
        ∫⁻ S, ENNReal.ofReal (bregman Φ (A S) b) ∂(Measure.pi fun _ : Fin m => P)
          ≤ ENNReal.ofReal (2 * σ ^ 2 / ((rhoBar - ρ) ^ 2 * m))) ∧
    -- (4.3)
    (Integrable (fun S : Fin m → Ω =>
        envelope Φ (popRisk P r f) rhoBar y - envelope Φ (empRisk r f S) rhoBar y)
        (Measure.pi fun _ : Fin m => P) ∧
      0 ≤ ∫ S, (envelope Φ (popRisk P r f) rhoBar y - envelope Φ (empRisk r f S) rhoBar y)
        ∂(Measure.pi fun _ : Fin m => P) ∧
      ∫ S, (envelope Φ (popRisk P r f) rhoBar y - envelope Φ (empRisk r f S) rhoBar y)
        ∂(Measure.pi fun _ : Fin m => P) ≤ 2 * σ ^ 2 / ((rhoBar - ρ) * m)) := by sorry

end GraphConvSubgrad.StatConc
