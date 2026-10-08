-- Prove2me | Theorems.Thm_MinimaxSLP_ObjSDP_recourseSet_bounded
-- name    : MinimaxSLP.ObjSDP.recourseSet_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:51.775545+00:00
-- url     : https://prove2.me/theorems/ed30a840-3efb-4a3f-b9e8-e7cfc6a9853b
-- title:
--   Proof of Theorem 2.1, p. 583 — under Assumption 3 the recourse set $X(x)$ is bounded and convex
-- statement:
--   Let $W\in\mathbb R^{r\times d}$, $T\in\mathbb R^{r\times n}$ and $h\in\mathbb R^r$, and assume that
--   $$
--   \{\pi\in\mathbb R^r : W'\pi\le q\}\neq\emptyset\qquad\text{for every } q\in\mathbb R^d
--   $$
--   (Assumption 3). Then for every $x\in\mathbb R^n$ the recourse set $X(x)=\{w\in\mathbb R^d : Ww=h-Tx,\ w\ge 0\}$ is a bounded convex set.
--
--   The paper uses this fact, without separate proof, to apply Sion's minimax theorem with $X(x)$ as the compact side.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 583, proof of Theorem 2.1 ("the set X(x) is a bounded convex set"); Assumption 3, p. 582

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjSDP_Model

open MeasureTheory Matrix

namespace MinimaxSLP.ObjSDP

/-- Proof of Theorem 2.1 (p. 583), "the set `X(x)` is a bounded convex set": if the dual
polyhedron `{π ∈ ℝ^r : W′π ≤ q}` is nonempty for every `q ∈ ℝ^d` (Assumption 3), then the
recourse set `X(x)` is bounded and convex, for every `x`. -/
theorem recourseSet_bounded {n r d : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q) (x : Fin n → ℝ) :
    Bornology.IsBounded (recourseSet W T h x) ∧ Convex ℝ (recourseSet W T h x) := by sorry

end MinimaxSLP.ObjSDP
