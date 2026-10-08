-- Prove2me | Theorems.Thm_KelsoCrawford_Process_lemma2_process_stops
-- name    : KelsoCrawford.Process.lemma2_process_stops
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:46:16.270929+00:00
-- url     : https://prove2.me/theorems/aaf0d255-35e0-4577-99a2-5dd94e0044ee
-- title:
--   Lemma 2 — after finitely many rounds every worker has exactly one offer and the process stops
-- statement:
--   Let a job-matching market with at least one firm satisfy regularity of utilities, (MP), (NFL), and (GS) for the discrete market with salary unit $\delta > 0$. Then for every run of the salary-adjustment process R1–R5 there is a round $T$ such that
--
--   $$\text{no rejections are issued in round } T, \quad \text{and every worker receives an offer from exactly one firm in round } T.$$
--
--   This is Lemma 2 of the paper ("After a finite number of rounds, every worker has exactly one offer and the process stops"). It is the "finite time" part of Theorem 1.
--
--   **Formalization Note** "After a finite number of rounds" is read as the existence of such a round $T$ for every run; no bound on $T$ is claimed, as the paper gives none.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1489, Lemma 2

import Mathlib
import Definitions.Def_KelsoCrawford_Process_Model
import Definitions.Def_KelsoCrawford_Process_Process

namespace KelsoCrawford.Process

/-- Lemma 2, p. 1489: after a finite number of rounds every worker has exactly one offer and the process stops. -/
theorem lemma2_process_stops
    {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (δ : ℝ) (hδ : 0 < δ) (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL)
    (hGS : ∀ j, GrossSubstitutesOn (M.y j) (M.gridVectors δ j)) :
    ∀ ρ : Run W F, M.IsRun δ ρ → ∃ T : ℕ, ρ.Stopped T ∧ ∀ i : W, ∃! j : F, i ∈ ρ.offers T j := by sorry

end KelsoCrawford.Process
