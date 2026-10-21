-- Prove2me | Theorems.Thm_IntertempDUI_Finite_lemma_B1
-- name    : IntertempDUI.Finite.lemma_B1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:10.656618+00:00
-- url     : https://prove2.me/theorems/c9591bbc-a60a-4539-a1f1-b1e83c169930
-- title:
--   Lemma B1 — utility trajectories are comeasurable
-- statement:
--   Let $\mathcal X$ be connected and let continuous $u$ represent synchronic preference: $x\succeq_{\mathrm{sy}}y$ exactly when $u(x)\ge u(y)$. If (MinEqn) holds, then the composition of $u$ with each feasible continuous trajectory is comeasurable with respect to time spans.
--
--   $$(MinEqn)\Longrightarrow u\circ\alpha\text{ is comeasurable for every }\alpha\in\mathcal A.$$
--
--   The statement is a step toward the finite-horizon characterization in Theorem 1.
-- source:
--   Pivato, Intertemporal choice with continuity constraints, SSRN 3232014 (August 10, 2018), p. 27, Lemma B1; https://ssrn.com/abstract=3232014

import Mathlib
import Definitions.Def_IntertempDUI_Finite_Content

namespace IntertempDUI.Finite

/-- Lemma B1, p. 27. -/
theorem lemma_B1 {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (T : ℝ) (hT : 0 < T) (A : Set (Traj T X))
    (hconst : ∀ x : X, ContinuousMap.const (Time T) x ∈ A)
    (pref : Pref T X) (hstd : Standing A pref)
    (u : X → ℝ) (hu : Continuous u)
    (hrep : ∀ x y : X, sy pref x y ↔ u y ≤ u x)
    (hM : MinEqn A pref) :
    ∀ a ∈ A, Comeasurable (u ∘ a) := by sorry

end IntertempDUI.Finite
