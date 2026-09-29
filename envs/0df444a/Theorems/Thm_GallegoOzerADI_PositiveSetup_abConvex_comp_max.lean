-- Prove2me | Theorems.Thm_GallegoOzerADI_PositiveSetup_abConvex_comp_max
-- name    : GallegoOzerADI.PositiveSetup.abConvex_comp_max
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:48:16.537583+00:00
-- url     : https://prove2.me/theorems/4c6b3579-6f98-48ba-be00-9561ba1d61b5
-- title:
--   Lemma 1, Part 5 — $g(\max(x,s)) \in C(a,b)$
-- statement:
--   Let $0 \le a < b$ and $g \in C(a,b)$, and let $s \in \mathbb{R}$ be such that
--
--   $$
--   g(s) + a \le g(x) + b \quad\text{for all } x \ge s.
--   $$
--
--   Then the function $f(x) = g(\max(x, s))$, which is constant equal to $g(s)$ to the left of $s$ and equal to $g$ to its right, also belongs to $C(a,b)$.
--
--   The paper singles this part out because it shortens the proof of Theorem 1: the optimal cost $J_t(x, o_t) = V_t(\max(s_t(o_t), x), o_t)$ of an $(s,S)$ policy has exactly this form, so $K$-convexity passes from $V_t$ to $J_t$.
--
--   **Formalization Note** The hypothesis $a < b$ is stated in the paper and kept, although the paper's proof does not use it.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1349, Lemma 1, Part 5 (proof p. 1358)

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex

namespace GallegoOzerADI.PositiveSetup

theorem abConvex_comp_max (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a < b) (g : ℝ → ℝ)
    (hg : ABConvex a b g) (s : ℝ) (hs : ∀ x, s ≤ x → g s + a ≤ g x + b) :
    ABConvex a b (fun x => g (max x s)) := by sorry

end GallegoOzerADI.PositiveSetup
