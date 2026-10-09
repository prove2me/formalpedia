-- Prove2me | Theorems.Thm_LearnNoConc_ERM_noise_correlation_nonneg
-- name    : LearnNoConc.ERM.noise_correlation_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:50:32.675407+00:00
-- url     : https://prove2.me/theorems/6e3a7578-84fa-408b-8597-caa51815b2d1
-- title:
--   §5, p. 23 — metric projection onto a convex class: Eξ(f − f*)(X) ≥ 0 for f ∈ F
-- statement:
--   Let $(X,Y)$ have joint law $\nu$ on $\Omega\times\mathbb R$, with $X\sim\mu$ and $\mathbb EY^2<\infty$. Let $F\subset L_2(\mu)$ be convex and let $f^*\in F$ minimize $\mathbb E(f(X)-Y)^2$ over $F$. With the noise $\xi=f^*(X)-Y$, for every $f\in F$,
--
--   $$\mathbb E\,\xi\,(f-f^*)(X)\ge0.$$
--
--   This is the variational characterization of the metric projection of $Y$ onto the convex set $\{f(X):f\in F\}$ in $L_2$; it is used in the proof of Theorem 3.1 to drop the mean of the multiplier term.
--
--   **Formalization Note** $\mathbb EY^2<\infty$ is added; it is presupposed by "$f^*$ minimizes $\mathbb E(f(X)-Y)^2$". All expectations are genuine integrals of integrable functions under these hypotheses.
-- source:
--   Mendelson, Learning without Concentration, arXiv:1401.0304v2, proof of Theorem 3.1, §5, p. 23, "by the characterization of the metric projection onto a convex set in a Hilbert space"

import Mathlib
import Definitions.Def_LearnNoConc_ERM_Setting

namespace LearnNoConc.ERM

open MeasureTheory
open scoped ENNReal

/-- §5, p. 23: since `f*` minimizes `‖Y − f(X)‖_{L₂}` over the convex class `F`, the
metric-projection characterization gives `E ξ (f − f*)(X) ≥ 0` for every `f ∈ F`,
where `ξ = f*(X) − Y`. -/
theorem noise_correlation_nonneg {Ω : Type*} [MeasurableSpace Ω] (ν : Measure (Ω × ℝ))
    [IsProbabilityMeasure ν] (F : Set (Ω → ℝ)) (hF2 : ∀ f ∈ F, MemLp f 2 (ν.map Prod.fst))
    (hFconv : Convex ℝ F) (hY : MemLp (fun z : Ω × ℝ => z.2) 2 ν)
    (fstar : Ω → ℝ) (hfstar : fstar ∈ F)
    (hmin : ∀ f ∈ F, ∫ z, (fstar z.1 - z.2) ^ 2 ∂ν ≤ ∫ z, (f z.1 - z.2) ^ 2 ∂ν) :
    ∀ f ∈ F, 0 ≤ ∫ z, (fstar z.1 - z.2) * (f z.1 - fstar z.1) ∂ν := by sorry

end LearnNoConc.ERM
