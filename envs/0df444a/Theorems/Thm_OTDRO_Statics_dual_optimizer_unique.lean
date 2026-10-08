-- Prove2me | Theorems.Thm_OTDRO_Statics_dual_optimizer_unique
-- name    : OTDRO.Statics.dual_optimizer_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:15:13.69477+00:00
-- url     : https://prove2.me/theorems/2655c09d-a785-4a3e-a8b3-2b4383370b6a
-- title:
--   §5.4 — uniqueness of the dual minimizer for small δ
-- statement:
--   Under Assumptions 1–5, fix a nonzero $\beta\in B$. There is a threshold $\delta_1\in(0,\delta_0)$ such that, for every $\delta\in(0,\delta_1)$, the minimization of the dual objective over nonnegative $\lambda$ has exactly one solution:
--
--   $$\exists!\,\lambda_*(\delta)\ge0:\quad f_\delta(\beta,\lambda_*(\delta))=\min_{\lambda\ge0}f_\delta(\beta,\lambda).$$
--
--   Every such optimizer also satisfies $\lambda_*(\delta)>\lambda'_{\rm thr}(\beta)$. This makes the dual optimizer a function of the ambiguity radius in the pointwise unique-maximizer regime needed for comparative statics.
--
--   **Formalization Note** The bounds $\underline L,\overline L$ are any admissible Lemma 6 pair; $\delta_1$ is chosen before $\delta$. Assumption 5 is needed for the Theorem 4 strong-convexity argument used on p. 41.
-- source:
--   arXiv:1810.02403v3, §5.4, proof of Theorem 7, p. 41, opening paragraph

import Mathlib
import Definitions.Def_OTDRO_Statics_Regions

namespace OTDRO.Statics

open MeasureTheory

/-- The uniqueness assertion in §5.4, proof of Theorem 7, p. 41. -/
theorem dual_optimizer_unique {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B)
    (hB4 : OTDRO.StrongCvx.Assumption4 B) (hBne : B.Nonempty)
    (M : ℝ) (h3 : OTDRO.StrongCvx.Assumption3 P0 ℓ B M)
    (h5 : OTDRO.StrongCvx.Assumption5 P0 ℓ B)
    (Llow Lbar : ℝ)
    (hL : 0 < Llow ∧ ∀ β ∈ B,
      Llow ≤ ∫ x, (deriv ℓ (inner ℝ β x)) ^ 2 ∂P0 ∧
      ∫ x, (deriv ℓ (inner ℝ β x)) ^ 2 ∂P0 ≤ Lbar)
    (β : EuclideanSpace ℝ (Fin d)) (hβB : β ∈ B) (hβ : β ≠ 0) :
    ∃ δ1 : ℝ, 0 < δ1 ∧ δ1 < OTDRO.StrongCvx.delta0 ρmin ρmax Llow (Rβ B) M ∧
      ∀ δ ∈ Set.Ioo 0 δ1,
        (∃! lam : ℝ, 0 ≤ lam ∧
          IsMinOn (fun l => OTDRO.Dual.fDelta P0 ℓ A δ β l) (Set.Ici 0) lam) ∧
        ∀ lam : ℝ, 0 ≤ lam →
          IsMinOn (fun l => OTDRO.Dual.fDelta P0 ℓ A δ β l) (Set.Ici 0) lam →
          OTDRO.Dual.lamThr' P0 A M δ β < lam := by sorry

end OTDRO.Statics
