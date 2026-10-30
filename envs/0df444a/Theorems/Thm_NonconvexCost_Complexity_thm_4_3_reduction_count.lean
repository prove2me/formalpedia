-- Prove2me | Theorems.Thm_NonconvexCost_Complexity_thm_4_3_reduction_count
-- name    : NonconvexCost.Complexity.thm_4_3_reduction_count
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:39.43781+00:00
-- url     : https://prove2.me/theorems/ade5a97d-4bcd-4756-b01b-7b9b8335b683
-- title:
--   Proof of Theorem 4.3, p. 10 — Algorithm 4.1 makes at most ⌈3(f(x₀) − min f)/(δε)⌉ reduction steps
-- statement:
--   Let $\delta,\epsilon>0$, let $C\subset X$, let $f$ be bounded below on $C$, and let $x_0\in C$ satisfy
--   $$x\in C,\ f(x)\le f(x_0),\ |y|\le\delta\ \Longrightarrow\ x+y\in C .$$
--   Let $G\colon X\times X\to X$ and $g_0\in X$ be arbitrary. Then for every $n$, among the first $n$ steps of the run of Algorithm 4.1 from $(x_0,g_0)$ the number of reduction steps (steps at which a trial point has just been accepted) is at most
--   $$\Big\lceil\frac{3}{\delta\epsilon}\big(f(x_0)-\inf_C f\big)\Big\rceil .$$
--
--   Each reduction step decreases the objective by at least $\delta\epsilon/3$ and the iterates stay in $C$, where $f$ is bounded below.
--
--   **Formalization Note** "$\min f$" is read as the infimum of $f$ over $C$ (the paper only assumes $f$ bounded below). A reduction step is counted by the state machine's re-initialisation phase. No hypothesis on $G$ is needed.
-- source:
--   Kong, Lewis, The cost of nonconvexity in deterministic nonsmooth optimization, arXiv:2210.00652v2, p. 10, proof of Theorem 4.3

import Mathlib
import Definitions.Def_NonconvexCost_Complexity_Setting
import Definitions.Def_NonconvexCost_Complexity_Algorithm

namespace NonconvexCost.Complexity

open Classical in
theorem thm_4_3_reduction_count {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (C : Set X) (f : X → ℝ) (hbdd : BddBelow (f '' C))
    (G : X → X → X) (x0 : X) (hx0 : x0 ∈ C)
    (hsub : ∀ x ∈ C, f x ≤ f x0 → ∀ y : X, ‖y‖ ≤ δ → x + y ∈ C) (g0 : X) (n : ℕ) :
    ((Finset.range n).filter (fun j => IsReinit (run f G δ ε x0 g0 j))).card ≤
      ⌈3 * (f x0 - sInf (f '' C)) / (δ * ε)⌉₊ := by sorry

end NonconvexCost.Complexity
