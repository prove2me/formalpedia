-- Prove2me | Theorems.Thm_IntertempDUI_Finite_lemma_A9
-- name    : IntertempDUI.Finite.lemma_A9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:30.299703+00:00
-- url     : https://prove2.me/theorems/5c8b7477-e9ea-406a-ae3a-9779456fabca
-- title:
--   Lemma A9 — richness for restricted trajectories
-- statement:
--   Under span richness and the two strengthened separability conditions, any feasible restrictions on disjoint spans can be combined into a feasible restriction on their Boolean join, agreeing on one span and remaining indifferent on the other.
--
--   $$(R^*)\wedge(LSep^*)\wedge(ISep^*)\Longrightarrow(Rch).$$
--
--   The statement is a step toward the finite-horizon characterization in Theorem 1.
-- source:
--   Pivato, Intertemporal choice with continuity constraints, SSRN 3232014 (August 10, 2018), p. 25, Lemma A9; https://ssrn.com/abstract=3232014

import Mathlib
import Definitions.Def_IntertempDUI_Finite_Axioms

namespace IntertempDUI.Finite

/-- Lemma A9, p. 25. -/
theorem lemma_A9 {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (T : ℝ) (hT : 0 < T) (A : Set (Traj T X))
    (hconst : ∀ x : X, ContinuousMap.const (Time T) x ∈ A)
    (pref : Pref T X) (hstd : Standing A pref)
    (hR : RichnessStar A pref) (hL : LSepStar A pref) (hI : ISepStar A pref) :
    Rch A pref := by sorry

end IntertempDUI.Finite
