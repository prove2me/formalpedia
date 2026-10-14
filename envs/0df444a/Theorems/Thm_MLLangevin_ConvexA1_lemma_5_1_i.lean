-- Prove2me | Theorems.Thm_MLLangevin_ConvexA1_lemma_5_1_i
-- name    : MLLangevin.ConvexA1.lemma_5_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:18.041577+00:00
-- url     : https://prove2.me/theorems/7e6fde6a-f7a5-4f70-94d5-a2110f661fa9
-- title:
--   Lemma 5.1 (i), p. 28 — 𝔼|X̄^{γ,x}_t − x⋆|² ≤ |x − x⋆|²e^{−αt/2} + |b(x⋆)|²(1/L² + 2/α²) + 2σ²d/α, and π^γ exists uniquely
-- statement:
--   Let $b:\mathbb R^d\to\mathbb R^d$ be $L$-Lipschitz and satisfy $(\mathbf C_\alpha)$, $\langle b(y)-b(x),y-x\rangle\le-\alpha|x-y|^2$, with $0<\alpha\le L$, and let $\sigma>0$. Let $W$ be a standard $d$-dimensional Brownian motion and $\bar X^{\gamma,x}$ the continuous-time additive Euler scheme with step $\gamma$ started at $x$ and driven by $W$. Fix $x^\star\in\mathbb R^d$ and $\gamma\in(0,\alpha/(2L^2)]$.
--
--   1. For every $t\ge0$ and $x\in\mathbb R^d$,
--   $$\mathbb E\big[|\bar X^{\gamma,x}_t-x^\star|^2\big]\le|x-x^\star|^2e^{-\frac\alpha2t}+|b(x^\star)|^2\Big(\frac1{L^2}+\frac2{\alpha^2}\Big)+\frac{2\sigma^2d}\alpha.$$
--   2. The Euler scheme with step $\gamma$ has exactly one invariant probability distribution $\pi^\gamma$, and
--   $$\pi^\gamma\big(|\cdot-x^\star|^2\big)=\int|y-x^\star|^2\,\pi^\gamma(dy)\le|b(x^\star)|^2\Big(\frac1{L^2}+\frac2{\alpha^2}\Big)+\frac{2\sigma^2d}\alpha.$$
--
--   The moment bound is uniform in time and in the step; it is the stability estimate from which existence of $\pi^\gamma$ and the bounds on $c_4$ in $(\mathbf H_4)$ follow.
--
--   **Formalization Note** The left side is `eLpNorm (X̄_t − x⋆) 2 P ^ 2` in $[0,\infty]$. Invariance of $\pi^\gamma$ means $\int\mathbb P(\bar X^{\gamma,x}_\gamma\in A)\pi^\gamma(dx)=\pi^\gamma(A)$ for every Borel $A$. $\sigma>0$ is the standing assumption of §2.4 (non-degeneracy, used for uniqueness). The page's display bounding $\sup_\gamma\pi^\gamma(|\cdot-x^\star|^2)$ prints the constant $2|b(x^\star)|^2(\frac1{L^2}+\frac2{\alpha^2})+\frac{\sigma^2d}\alpha$ (and a garbled index set); the proof (p. 29, $\pi^\gamma(|\cdot-x^\star|^2)\le\limsup_t\mathbb E|\bar X_t-x^\star|^2$) gives the limit of (47), which is what is stated, for every $\gamma$ in the range (so for the supremum).
-- source:
--   Egéa–Panloup, Multilevel-Langevin pathwise average for Gibbs approximation, arXiv:2109.07753v2, Lemma 5.1 (i), (47), p. 28

import Mathlib
import Definitions.Def_MLLangevin_ConvexA1_Setting

namespace MLLangevin.ConvexA1

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped ENNReal NNReal

/-- Lemma 5.1 (i), p. 28: the second-moment bound (47) for the continuous-time additive Euler
scheme, existence and uniqueness of the invariant probability `π^γ` of the step-γ scheme, and the
bound on `π^γ(|· − x⋆|²)` (constants as the limit of (47) gives them; the printed display has
`2|b(x⋆)|²(…) + σ²d/α`, which does not follow from (47)). -/
theorem lemma_5_1_i {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → SDEState d) (hW : IsStandardBrownian P W)
    (b : SDEState d → SDEState d) (L α σ : ℝ) (hLip : ∀ x y, ‖b x - b y‖ ≤ L * ‖x - y‖)
    (hC : CondC b α) (hα : 0 < α) (hαL : α ≤ L) (hσ : 0 < σ)
    (xs : SDEState d) (γ : ℝ) (hγ : 0 < γ) (hγL : γ ≤ α / (2 * L ^ 2)) :
    (∀ (x : SDEState d) (t : ℝ≥0),
      eLpNorm (fun ω => eulerCont b σ γ x W t ω - xs) 2 P ^ 2 ≤
        ENNReal.ofReal (‖x - xs‖ ^ 2 * Real.exp (-(α / 2) * (t : ℝ)) +
          ‖b xs‖ ^ 2 * (1 / L ^ 2 + 2 / α ^ 2) + 2 * σ ^ 2 * (d : ℝ) / α)) ∧
    (∃! πγ : Measure (SDEState d), IsProbabilityMeasure πγ ∧ IsInvChain P b σ γ W πγ) ∧
    ∀ πγ : Measure (SDEState d), IsProbabilityMeasure πγ → IsInvChain P b σ γ W πγ →
      ∫⁻ y, ENNReal.ofReal (‖y - xs‖ ^ 2) ∂πγ ≤
        ENNReal.ofReal (‖b xs‖ ^ 2 * (1 / L ^ 2 + 2 / α ^ 2) + 2 * σ ^ 2 * (d : ℝ) / α) := by sorry

end MLLangevin.ConvexA1
