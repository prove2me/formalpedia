-- Prove2me | Theorems.Thm_KelsoCrawford_Process_process_well_defined
-- name    : KelsoCrawford.Process.process_well_defined
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:45:51.937926+00:00
-- url     : https://prove2.me/theorems/ac107de8-34b6-42e4-a1a4-ef313dac34bd
-- title:
--   Section 3, R2 — under (GS) the salary-adjustment process is well defined: a run of R1–R5 exists
-- statement:
--   Let a job-matching market with at least one firm satisfy regularity of utilities, (MP), (NFL), and (GS) for the discrete market with salary unit $\delta > 0$. Then
--
--   $$\text{there exists a run of the salary-adjustment process R1–R5 with unit } \delta.$$
--
--   The content is rule R2: in each round, every firm can choose a profit-maximizing set of workers that contains every offer it made in the previous round and that was not rejected. The paper justifies this in one sentence: "By (GS), the firm sacrifices no profits in doing this, since (by R4) other workers' permitted salaries cannot have fallen, and the salary of a worker who did not reject an offer remains constant." In round $0$ the offer to all workers is costless by (MP).
--
--   This statement is what makes the universally quantified results about runs (Lemmas 1–4 and Theorem 1) non-vacuous.
--
--   **Formalization Note** The paper takes the well-definedness of R2 for granted in the sentence quoted; here it is an explicit existence statement. The standing assumptions of p. 1486 are all hypotheses, and "at least one firm" is the paper's $n \ge 1$ (with no firms and some workers no run exists).
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), pp. 1488–1489, Section 3, rule R2 ("By (GS), the firm sacrifices no profits in doing this …")

import Mathlib
import Definitions.Def_KelsoCrawford_Process_Model
import Definitions.Def_KelsoCrawford_Process_Process

namespace KelsoCrawford.Process

/-- R2, pp. 1488–1489: under (GS) on the discrete market, the salary-adjustment process is well defined — a run of R1–R5 exists (at every round each firm has a favorite set containing all its unrejected offers). -/
theorem process_well_defined
    {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (δ : ℝ) (hδ : 0 < δ) (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL)
    (hGS : ∀ j, GrossSubstitutesOn (M.y j) (M.gridVectors δ j)) :
    ∃ ρ : Run W F, M.IsRun δ ρ := by sorry

end KelsoCrawford.Process
