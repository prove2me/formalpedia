-- Prove2me | Theorems.Thm_IntertempDUI_Finite_lemma_A4
-- name    : IntertempDUI.Finite.lemma_A4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:19.865173+00:00
-- url     : https://prove2.me/theorems/608c1d2f-a5d1-40fa-b120-f09c2de116ab
-- title:
--   Lemma A4 — (LSep*) and (LSep)
-- statement:
--   For a feasible set and interval preference structure satisfying span richness, existence of a suitable intermittent preference order family is equivalent to limited separability of the primitive orders.
--
--   $$(R^*)\Longrightarrow\bigl((LSep^*)\Longleftrightarrow(LSep)\bigr).$$
--
--   The statement is a step toward the finite-horizon characterization in Theorem 1.
-- source:
--   Pivato, Intertemporal choice with continuity constraints, SSRN 3232014 (August 10, 2018), p. 22, Lemma A4; https://ssrn.com/abstract=3232014

import Mathlib
import Definitions.Def_IntertempDUI_Finite_Axioms

namespace IntertempDUI.Finite

/-- Lemma A4, p. 22. -/
theorem lemma_A4 {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (T : ℝ) (hT : 0 < T) (A : Set (Traj T X))
    (hconst : ∀ x : X, ContinuousMap.const (Time T) x ∈ A)
    (pref : Pref T X) (hstd : Standing A pref) (hR : RichnessStar A pref) :
    LSepStar A pref ↔ LSep A pref := by sorry

end IntertempDUI.Finite
