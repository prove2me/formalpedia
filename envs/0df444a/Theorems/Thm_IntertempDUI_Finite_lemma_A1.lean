-- Prove2me | Theorems.Thm_IntertempDUI_Finite_lemma_A1
-- name    : IntertempDUI.Finite.lemma_A1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:59.403262+00:00
-- url     : https://prove2.me/theorems/eabedecf-5471-4773-b760-18cc33e1dd3b
-- title:
--   Lemma A1 — equivalence of (R*) and (R)
-- statement:
--   On a finite time interval, for a feasible set and an intertemporal preference structure satisfying the standing assumptions, the span richness condition and interval richness condition are equivalent.
--
--   $$(R^*)\Longleftrightarrow(R).$$
--
--   The statement is a step toward the finite-horizon characterization in Theorem 1.
-- source:
--   Pivato, Intertemporal choice with continuity constraints, SSRN 3232014 (August 10, 2018), p. 20, Lemma A1; https://ssrn.com/abstract=3232014

import Mathlib
import Definitions.Def_IntertempDUI_Finite_Axioms

namespace IntertempDUI.Finite

/-- Lemma A1, p. 20. -/
theorem lemma_A1 {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (T : ℝ) (hT : 0 < T) (A : Set (Traj T X))
    (hconst : ∀ x : X, ContinuousMap.const (Time T) x ∈ A)
    (pref : Pref T X) (hstd : Standing A pref) :
    RichnessStar A pref ↔ Richness A pref := by sorry

end IntertempDUI.Finite
