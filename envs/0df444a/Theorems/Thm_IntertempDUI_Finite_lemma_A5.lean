-- Prove2me | Theorems.Thm_IntertempDUI_Finite_lemma_A5
-- name    : IntertempDUI.Finite.lemma_A5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:06.136167+00:00
-- url     : https://prove2.me/theorems/28000b7b-2924-487a-ae7f-b1b9cdc48f3c
-- title:
--   Lemma A5 — induced and primitive interval orders agree
-- statement:
--   Assume (R*), (ISep), and (LSep*). For each time interval $\mathcal J$, its primitive intertemporal preference order agrees with the intermittent order induced on that same interval. Equality is tested on feasible restricted trajectories.
--
--   $$\succeq_{\mathcal J}^{\mathrm{primitive}}=\succeq_{\mathcal J}^{\mathrm{induced}}.$$
--
--   The statement is a step toward the finite-horizon characterization in Theorem 1.
-- source:
--   Pivato, Intertemporal choice with continuity constraints, SSRN 3232014 (August 10, 2018), p. 22, Lemma A5; https://ssrn.com/abstract=3232014

import Mathlib
import Definitions.Def_IntertempDUI_Finite_Axioms

namespace IntertempDUI.Finite

/-- Lemma A5, p. 22. -/
theorem lemma_A5 {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (T : ℝ) (hT : 0 < T) (A : Set (Traj T X))
    (hconst : ∀ x : X, ContinuousMap.const (Time T) x ∈ A)
    (pref : Pref T X) (hstd : Standing A pref)
    (hR : RichnessStar A pref) (hI : ISep A pref) (hL : LSepStar A pref) :
    ∀ J, IsTimeInterval J → ∀ a ∈ A, ∀ b ∈ A,
      pref J a b ↔ induced A pref J a b := by sorry

end IntertempDUI.Finite
