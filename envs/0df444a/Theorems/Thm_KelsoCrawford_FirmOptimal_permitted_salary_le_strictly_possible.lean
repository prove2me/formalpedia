-- Prove2me | Theorems.Thm_KelsoCrawford_FirmOptimal_permitted_salary_le_strictly_possible
-- name    : KelsoCrawford.FirmOptimal.permitted_salary_le_strictly_possible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:36:26.112861+00:00
-- url     : https://prove2.me/theorems/c09372fc-509f-4ca9-94f5-757d3f641491
-- title:
--   Proof of Theorem 4, p. 1495 — permitted salaries never exceed the salaries of any strict core allocation
-- statement:
--   Consider a discrete market with salary unit $\delta > 0$ satisfying regularity, (MP), (NFL), (GS) for every firm on the permitted salary vectors, (NTW) and (NTF). Let $(f; s_{1f(1)}, \dots, s_{mf(m)})$ be any discrete strict core allocation. In any run of the salary-adjustment process R1–R5, for every round $t$ and every worker $i$,
--
--   $$s_{i f(i)}(t) \le s_{i f(i)}.$$
--
--   In words: every set of workers who are strictly possible for a firm in a strict core allocation is available to that firm, in every round, at permitted salaries no bigger than those at which they are strictly possible.
--
--   **Formalization Note** The strict core allocation pays permitted (grid) salaries, as D2 requires. Every run and every round are covered.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1495, proof of Theorem 4, third paragraph

import Mathlib
import Definitions.Def_KelsoCrawford_FirmOptimal_Model
import Definitions.Def_KelsoCrawford_FirmOptimal_Process
import Definitions.Def_KelsoCrawford_FirmOptimal_NoTies

namespace KelsoCrawford.FirmOptimal

theorem permitted_salary_le_strictly_possible
    {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (δ : ℝ) (hδ : 0 < δ) (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL)
    (hGS : ∀ j, KelsoCrawford.Process.GrossSubstitutesOn (M.y j) (M.gridVectors δ j))
    (hNTW : M.NTW δ) (hNTF : M.NTF δ) :
    ∀ ρ : Run W F, M.IsRun δ ρ → ∀ (t : ℕ) (A : Allocation W F), M.IsStrictCore (M.grid δ) A →
      ∀ i, ρ.sal t i (A.assign i) ≤ A.sal i := by sorry

end KelsoCrawford.FirmOptimal
