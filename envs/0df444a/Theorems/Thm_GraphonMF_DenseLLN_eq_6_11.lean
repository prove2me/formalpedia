-- Prove2me | Theorems.Thm_GraphonMF_DenseLLN_eq_6_11
-- name    : GraphonMF.DenseLLN.eq_6_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:44.36717+00:00
-- url     : https://prove2.me/theorems/7dd97139-25dd-4701-8d65-09b8cc88bbb0
-- title:
--   (6.11), p. 3607 — limsup ∫₀ᵀ T^{n,3}_s ds ≤ κ(M) limsup ‖G_n − G‖ + κ/M^ε
-- statement:
--   Assume Conditions 2.1 and 2.2 (for a cover $I_1,\dots,I_N$), let $G$ be a graphon and let $X$ solve the graphon particle system (2.1) with laws $\mu_u$. For step graphons $G_n$ (Condition 3.1(a)) let
--   $$\mathcal T^{n,3}_s=\frac1n\sum_{i=1}^n\mathbb E\Big|\frac1n\sum_{j=1}^n\int_{\mathbb R^d}b(X_{i/n}(s),x)G_n(\tfrac in,\tfrac jn)\mu_{j/n,s}(dx)-\int_I\!\int_{\mathbb R^d}b(X_{i/n}(s),x)G(\tfrac in,v)\mu_{v,s}(dx)\,dv\Big|^2 .$$
--   Then there is $\kappa$ and, for each $M>0$, a $\kappa(M)$ such that for every sequence of step graphons $(G_n)$,
--   $$\limsup_{n\to\infty}\int_0^T\mathcal T^{n,3}_s\,ds\le\kappa(M)\limsup_{n\to\infty}\|G_n-G\|+\frac{\kappa}{M^{\varepsilon}},$$
--   where $\|\cdot\|$ is the operator norm $L^\infty(I)\to L^1(I)$ and $\varepsilon$ is the exponent of Condition 2.1.
--
--   This bounds the graphon-discretization error in the proof of Lemma 6.1. It collects the truncation and approximation estimates (6.5)–(6.10).
--
--   **Formalization Note** The constants come before the sequence $(G_n)$; the page says $\kappa(M)$ "depends on $M$ but not on $n$". Both sides are computed in $[0,\infty]$, so the limsups need no boundedness side conditions. The time integral is the Lebesgue integral over $[0,T]$.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3607, (6.11) (with (6.2), p. 3605)

import Mathlib
import Definitions.Def_GraphonMF_DenseLLN_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.DenseLLN
theorem eq_6_11 {Ω : Type*} [MeasurableSpace Ω] {T : ℝ≥0} {d N : ℕ} {P : Measure Ω}
    {μ0 : GraphonMF.Stability.I → Measure (GraphonMF.Stability.State d)} {X0 : GraphonMF.Stability.I → Ω → GraphonMF.Stability.State d} {B : GraphonMF.Stability.I → ℝ≥0 → Ω → GraphonMF.Stability.State d}
    (noise : NoiseSetting P μ0 X0 B) (hT : 0 < T)
    (b : GraphonMF.Stability.State d → GraphonMF.Stability.State d → GraphonMF.Stability.State d) (σ : GraphonMF.Stability.State d → GraphonMF.Stability.State d → Matrix (Fin d) (Fin d) ℝ)
    (ε : ℝ) (h21 : GraphonMF.Stability.Cond21 ε μ0 b σ)
    (J : Fin N → Set GraphonMF.Stability.I) (h22a : Cond22a μ0 J)
    (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (hG : GraphonMF.Stability.IsGraphon G) (h22b : Cond22b G J)
    (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d) (hX : IsGraphonSolution noise G b σ X) :
    ∃ κ : ℝ, ∀ M : ℝ, 0 < M → ∃ κM : ℝ, ∀ Gs : ℕ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ,
      (∀ n, 0 < n → GraphonMF.Stability.IsStepGraphon n (Gs n)) →
      limsup (fun n => ∫⁻ s in Set.Icc (0 : ℝ) T, Tn3 P G b X Gs n s.toNNReal) atTop ≤
        ENNReal.ofReal κM *
            limsup (fun n => ENNReal.ofReal (GraphonMF.Stability.opNorm (fun u v => Gs n u v - G u v))) atTop +
          ENNReal.ofReal (κ / M ^ ε) := by sorry
end GraphonMF.DenseLLN
