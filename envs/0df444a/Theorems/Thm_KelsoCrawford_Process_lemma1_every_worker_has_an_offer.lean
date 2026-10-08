-- Prove2me | Theorems.Thm_KelsoCrawford_Process_lemma1_every_worker_has_an_offer
-- name    : KelsoCrawford.Process.lemma1_every_worker_has_an_offer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:46:09.264719+00:00
-- url     : https://prove2.me/theorems/a4415873-16f2-4506-bb42-e3a20e35a377
-- title:
--   Lemma 1 — every worker has at least one offer in every period
-- statement:
--   Let a job-matching market with at least one firm satisfy regularity of utilities, (MP), (NFL), and (GS) for the discrete market with salary unit $\delta > 0$. Then along every run of the salary-adjustment process R1–R5,
--
--   $$\text{for every round } t \text{ and every worker } i, \text{ some firm makes } i \text{ an offer in round } t.$$
--
--   This is Lemma 1 of the paper; it ensures that the allocation read off when the process stops assigns every worker to a firm that is actually making him or her an offer.
--
--   **Formalization Note** The statement is for every run, i.e. for every tie-breaking by firms and workers allowed by R2 and R3.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1489, Lemma 1

import Mathlib
import Definitions.Def_KelsoCrawford_Process_Model
import Definitions.Def_KelsoCrawford_Process_Process

namespace KelsoCrawford.Process

/-- Lemma 1, p. 1489: every worker has at least one offer in every period. -/
theorem lemma1_every_worker_has_an_offer
    {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (δ : ℝ) (hδ : 0 < δ) (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL)
    (hGS : ∀ j, GrossSubstitutesOn (M.y j) (M.gridVectors δ j)) :
    ∀ ρ : Run W F, M.IsRun δ ρ → ∀ (t : ℕ) (i : W), ∃ j, i ∈ ρ.offers t j := by sorry

end KelsoCrawford.Process
