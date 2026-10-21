-- Prove2me | Theorems.Thm_IntertempDUI_Finite_proposition_A6
-- name    : IntertempDUI.Finite.proposition_A6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:25.197587+00:00
-- url     : https://prove2.me/theorems/9e0315d5-97d4-4a8c-8f0b-ad49850f5642
-- title:
--   Proposition A6 — separability of intermittent preferences
-- statement:
--   If the feasible trajectories and interval preferences satisfy span richness, strengthened interval separability, and the intermittent-order extension condition, then the induced intermittent preferences satisfy separability (Sep).
--
--   $$(R^*)\wedge(ISep^*)\wedge(LSep^*)\Longrightarrow(Sep).$$
--
--   The statement is a step toward the finite-horizon characterization in Theorem 1.
-- source:
--   Pivato, Intertemporal choice with continuity constraints, SSRN 3232014 (August 10, 2018), p. 23, Proposition A6; https://ssrn.com/abstract=3232014

import Mathlib
import Definitions.Def_IntertempDUI_Finite_Axioms

namespace IntertempDUI.Finite

/-- Proposition A6, p. 23. -/
theorem proposition_A6 {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (T : ℝ) (hT : 0 < T) (A : Set (Traj T X))
    (hconst : ∀ x : X, ContinuousMap.const (Time T) x ∈ A)
    (pref : Pref T X) (hstd : Standing A pref)
    (hR : RichnessStar A pref) (hI : ISepStar A pref) (hL : LSepStar A pref) :
    Sep A pref := by sorry

end IntertempDUI.Finite
