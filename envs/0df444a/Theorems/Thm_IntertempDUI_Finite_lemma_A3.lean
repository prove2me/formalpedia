-- Prove2me | Theorems.Thm_IntertempDUI_Finite_lemma_A3
-- name    : IntertempDUI.Finite.lemma_A3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:10.507497+00:00
-- url     : https://prove2.me/theorems/3c862c95-5ef1-4673-b344-8060f15585a7
-- title:
--   Lemma A3 — (ISep*) and (ISep)
-- statement:
--   The stronger interval-separability condition implies ordinary interval separability. On a finite horizon, under richness (R), the two conditions are equivalent.
--
--   $$(ISep^*)\Longrightarrow(ISep),\qquad (R)\Longrightarrow\bigl((ISep)\Longleftrightarrow(ISep^*)\bigr).$$
--
--   The statement is a step toward the finite-horizon characterization in Theorem 1.
-- source:
--   Pivato, Intertemporal choice with continuity constraints, SSRN 3232014 (August 10, 2018), p. 21, Lemma A3; https://ssrn.com/abstract=3232014

import Mathlib
import Definitions.Def_IntertempDUI_Finite_Axioms

namespace IntertempDUI.Finite

/-- Lemma A3, p. 21. -/
theorem lemma_A3 {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (T : ℝ) (hT : 0 < T) (A : Set (Traj T X))
    (hconst : ∀ x : X, ContinuousMap.const (Time T) x ∈ A)
    (pref : Pref T X) (hstd : Standing A pref) :
    (ISepStar A pref → ISep A pref) ∧
    (Richness A pref → (ISep A pref ↔ ISepStar A pref)) := by sorry

end IntertempDUI.Finite
