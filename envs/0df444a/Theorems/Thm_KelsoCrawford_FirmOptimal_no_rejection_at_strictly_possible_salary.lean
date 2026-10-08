-- Prove2me | Theorems.Thm_KelsoCrawford_FirmOptimal_no_rejection_at_strictly_possible_salary
-- name    : KelsoCrawford.FirmOptimal.no_rejection_at_strictly_possible_salary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:36:23.90924+00:00
-- url     : https://prove2.me/theorems/2961c7e1-549b-4efc-b8e8-a36445a57036
-- title:
--   Proof of Theorem 4, p. 1495 — no worker ever rejects a firm at a salary at which he or she is strictly possible for it
-- statement:
--   Consider a discrete market with salary unit $\delta > 0$ satisfying regularity, (MP), (NFL), (GS) for every firm on the permitted salary vectors, (NTW) and (NTF). In any run of the salary-adjustment process R1–R5, if worker $i$ rejects firm $j$ in round $t$, where $j$'s permitted salary for $i$ is $s_{ij}(t)$, then
--
--   $$i \text{ is not strictly } s_{ij}(t)\text{-possible for } j,$$
--
--   i.e. no discrete strict core allocation assigns $i$ to $j$ at salary $s_{ij}(t)$.
--
--   This is the key step in showing that the process favors the firms: rejections only ever happen at salaries above every strict core salary.
--
--   **Formalization Note** Every run (every tie-breaking) and every round are covered. The hypotheses are those of Theorem 4.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1495, proof of Theorem 4, third paragraph

import Mathlib
import Definitions.Def_KelsoCrawford_FirmOptimal_Model
import Definitions.Def_KelsoCrawford_FirmOptimal_Process
import Definitions.Def_KelsoCrawford_FirmOptimal_NoTies

namespace KelsoCrawford.FirmOptimal

theorem no_rejection_at_strictly_possible_salary
    {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (δ : ℝ) (hδ : 0 < δ) (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL)
    (hGS : ∀ j, KelsoCrawford.Process.GrossSubstitutesOn (M.y j) (M.gridVectors δ j))
    (hNTW : M.NTW δ) (hNTF : M.NTF δ) :
    ∀ ρ : Run W F, M.IsRun δ ρ → ∀ t i j, ρ.Rejects t i j →
      ¬ M.StrictlyPossible δ i j (ρ.sal t i j) := by sorry

end KelsoCrawford.FirmOptimal
