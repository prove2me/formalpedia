-- Prove2me | Theorems.Thm_LearnNoConc_ERM_eq_5_5
-- name    : LearnNoConc.ERM.eq_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:47:58.153756+00:00
-- url     : https://prove2.me/theorems/7238a5ab-c55d-4db0-b3a9-52d064c8e233
-- title:
--   (5.5), p. 24 — from the sphere ‖f − f*‖ = α to ‖f − f*‖ ≥ α: |P_Nξ(f − f*) − Eξ(f − f*)| ≤ 4γ‖f − f*‖²
-- statement:
--   Let $(X,Y)$ have joint law $\nu$ on $\Omega\times\mathbb R$ with $X\sim\mu$ and $\mathbb EY^2<\infty$, let $F\subset L_2(\mu)$ be convex, $f^*\in F$, and $\xi=f^*(X)-Y$. Fix a sample $(X_i,Y_i)_{i=1}^N$ ($N\ge1$), with $\xi_i=f^*(X_i)-Y_i$, and write
--
--   $$D(f)=\frac1N\sum_{i=1}^N\xi_i(f-f^*)(X_i)-\mathbb E\,\xi(f-f^*)(X).$$
--
--   Let $\alpha>0$ and $\gamma\in\mathbb R$, and suppose that on this sample (5.4) holds: $|D(f)|\le4\gamma\alpha^2$ for every $f\in F$ with $\|f-f^*\|_{L_2}=\alpha$. Then every $f\in F$ with $\|f-f^*\|_{L_2}\ge\alpha$ satisfies
--
--   $$|D(f)|\le4\gamma\alpha^2\cdot\frac{\|f-f^*\|_{L_2}}{\alpha}\le4\gamma\|f-f^*\|_{L_2}^2.\tag{5.5}$$
--
--   The statement is deterministic: it extends a bound on the multiplier deviation from the sphere of radius $\alpha$ to everything outside it, using that $F-f^*$ is star-shaped.
--
--   **Formalization Note** The conclusion asserts the final inequality of (5.5), $|D(f)|\le4\gamma\|f-f^*\|_{L_2}^2$. $\mathbb EY^2<\infty$ is added (it is presupposed by the definition of $f^*$ in the paper and makes $\mathbb E\xi(f-f^*)$ a genuine integral).
-- source:
--   Mendelson, Learning without Concentration, arXiv:1401.0304v2, proof of Theorem 3.1, display (5.5), p. 24 (hypothesis: display (5.4), p. 24)

import Mathlib
import Definitions.Def_LearnNoConc_ERM_Setting

namespace LearnNoConc.ERM

open MeasureTheory
open scoped ENNReal

/-- Display (5.5), p. 24 (deterministic, one fixed sample `z`): if the bound (5.4)
`|P_N ξ(f − f*) − E ξ(f − f*)| ≤ 4γα²` holds on the sphere `‖f − f*‖_{L₂} = α`, then
`|P_N ξ(f − f*) − E ξ(f − f*)| ≤ 4γ ‖f − f*‖²_{L₂}` whenever `‖f − f*‖_{L₂} ≥ α`. -/
theorem eq_5_5 {Ω : Type*} [MeasurableSpace Ω] (ν : Measure (Ω × ℝ)) [IsProbabilityMeasure ν]
    (F : Set (Ω → ℝ)) (hF2 : ∀ f ∈ F, MemLp f 2 (ν.map Prod.fst)) (hFconv : Convex ℝ F)
    (hY : MemLp (fun z : Ω × ℝ => z.2) 2 ν) (fstar : Ω → ℝ) (hfstar : fstar ∈ F)
    (N : ℕ) (hN : 0 < N) (z : Fin N → Ω × ℝ) (γ α : ℝ) (hα : 0 < α)
    (h54 : ∀ f ∈ F, eLpNorm (f - fstar) 2 (ν.map Prod.fst) = ENNReal.ofReal α →
      |multDev ν fstar z f| ≤ 4 * γ * α ^ 2) :
    ∀ f ∈ F, ENNReal.ofReal α ≤ eLpNorm (f - fstar) 2 (ν.map Prod.fst) →
      |multDev ν fstar z f|
        ≤ 4 * γ * ((eLpNorm (f - fstar) 2 (ν.map Prod.fst)).toReal) ^ 2 := by sorry

end LearnNoConc.ERM
