-- Prove2me | Theorems.Thm_KelsoCrawford_ContinuousCore_fine_grid_improves
-- name    : KelsoCrawford.ContinuousCore.fine_grid_improves
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:51.040187+00:00
-- url     : https://prove2.me/theorems/56ed537b-3edc-4706-9867-0cb13bd4038b
-- title:
--   Section 4 — a grid finer than H/(m + 1) inherits the improvement
-- statement:
--   Suppose a finite market has regular utilities, (MP), (NFL), the reservation-salary relation, and continuous gross substitutes. Let $H>0$ be a gain that every individually rational allocation admits: some coalition can leave all its workers no worse off while increasing its firm’s profit by at least $H$. If $m$ is the number of workers and
--
--   $$0<\delta<\frac{H}{m+1},$$
--
--   then every individually rational allocation paying salaries on the $\delta$-grid admits a coalition that strictly improves every worker in that coalition and its firm using salaries on the same grid.
--
--   This is the discretization step that conflicts with the discrete core existence fact.
--
--   **Formalization Note** The denominator is a real number $m+1$. The grid begins at each worker–firm reservation salary; no inverse utility function is used.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), pp. 1491–1492, Section 4, proof of Theorem 2, concluding sentence

import Mathlib
import Definitions.Def_KelsoCrawford_ContinuousCore_Model

namespace KelsoCrawford.ContinuousCore

theorem fine_grid_improves {W F : Type}
    [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL)
    (hres : M.ReservationSalaries)
    (hGS : ∀ j, KelsoCrawford.Process.GrossSubstitutesOn (M.y j) Set.univ)
    (H : ℝ) (hH : 0 < H)
    (hgain : ∀ A : Allocation W F, M.IsIR A →
      ∃ (j : F) (C : Finset W) (r : W → ℝ),
        (∀ i ∈ C, M.u i (A.assign i) (A.sal i) ≤ M.u i j (r i)) ∧
        KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal + H ≤ KelsoCrawford.Process.profit (M.y j) C r)
    (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ < H / ((Fintype.card W : ℝ) + 1))
    (A : Allocation W F) (hIR : M.IsIR A)
    (hgrid : ∀ i, A.sal i ∈ M.grid δ i (A.assign i)) :
    M.CanStrictlyImprove (M.grid δ) A := by sorry

end KelsoCrawford.ContinuousCore
