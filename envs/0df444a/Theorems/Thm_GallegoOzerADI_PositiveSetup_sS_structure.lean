-- Prove2me | Theorems.Thm_GallegoOzerADI_PositiveSetup_sS_structure
-- name    : GallegoOzerADI.PositiveSetup.sS_structure
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:49:36.742643+00:00
-- url     : https://prove2.me/theorems/81ce6bd6-45be-4ca5-b3cc-418d511e49e8
-- title:
--   Corollary 1 — ordering up to $S$ is optimal iff $x \le s$, and $J(x) = V(\max(s, x))$
-- statement:
--   Let $K > 0$ and let $V : \mathbb{R} \to \mathbb{R}$ be continuous and satisfy the conditions of Lemma 2: $V \in C(0,K)$, $V$ has a global minimizer $S$, and $V(x) > K + V(S)$ for some $x < S$. Write $H(x) = K + \min_{y \ge x}V(y) - V(x)$ and $J(x) = \min_{y \ge x}\{K\delta(y - x) + V(y)\}$. Then there is a finite $s$ such that
--
--   1. $s = \max\{x : H(x) \le 0\}$;
--   2. for every $x$, it is optimal to order up to $S$ from $x$ (that is, $x < S$ and $K + V(S) = J(x)$) if and only if $x \le s$;
--   3. the optimal value is
--   $$
--   J(x) = V(\max(s, x)) \quad\text{for all } x. \qquad (10)
--   $$
--
--   This is the $(s,S)$ structure of a single-period ordering problem with a $K$-convex cost-to-go: order up to $S$ when the inventory position is at or below $s$, do not order otherwise.
--
--   **Formalization Note** The paper states the corollary for $V_t(\cdot, o_t)$ at a fixed period and observed-demand vector; it is formalized for an arbitrary function $V$. Continuity of $V$ is added: the paper uses it without stating it (without continuity the maximum defining $s$ need not exist, and (10) can fail at $x = s$). In the dynamic program continuity of $V_t$ is a consequence of the model, not an assumption. The "order up to $S$ iff $x \le s$" clause is stated as a biconditional in $x$; ordering up to $S$ from $x$ requires $S > x$, since otherwise no order is placed.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1350, Corollary 1 and Eq. (10)

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex
import Definitions.Def_GallegoOzerADI_PositiveSetup_SetupCost

namespace GallegoOzerADI.PositiveSetup

theorem sS_structure (K : ℝ) (hK : 0 < K) (V : ℝ → ℝ) (hV : ABConvex 0 K V)
    (hcont : Continuous V) (S : ℝ) (hS : ∀ x, V S ≤ V x)
    (hiii : ∃ x, x < S ∧ K + V S < V x) :
    ∃ s : ℝ, IsGreatest {x | reorderGap K V x ≤ 0} s ∧
      (∀ x, (x < S ∧ orderCost K V x = K + V S) ↔ x ≤ s) ∧
      ∀ x, orderCost K V x = V (max s x) := by sorry

end GallegoOzerADI.PositiveSetup
