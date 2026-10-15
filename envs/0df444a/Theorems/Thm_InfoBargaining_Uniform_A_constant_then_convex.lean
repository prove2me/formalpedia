-- Prove2me | Theorems.Thm_InfoBargaining_Uniform_A_constant_then_convex
-- name    : InfoBargaining.Uniform.A_constant_then_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:57:29.004472+00:00
-- url     : https://prove2.me/theorems/fb4a9988-703e-4bd2-b136-bb2ba1f2d289
-- title:
--   Proof of Corollary 1, p. 30 — A(·, c) is constant for α ≤ |1 − 2c|, increasing for α ≥ |1 − 2c|, and convex
-- statement:
--   Let the prior be uniform on $[0,1]$ and $c\in(0,1)$. As a function of the informativeness $\alpha\in(0,1)$, the total ex ante surplus $A(\alpha,c)$ of (7):
--
--   1. is constant on $\{\alpha\in(0,1):\alpha\le|1-2c|\}$;
--   2. is strictly increasing on $\{\alpha\in(0,1):\alpha\ge|1-2c|\}$;
--   3. is convex on the whole interval $(0,1)$.
--
--   Convexity of $A$ in $\alpha$, together with a cost linear in $\alpha$, makes the buyer's objective convex, which forces the optimal information level to a corner of $[\underline\alpha,\bar\alpha]$.
--
--   **Formalization Note** The page says "increasing and convex in α for α ≥ |1 − 2c|". Item 2 states strict increase, and item 3 states convexity on all of $(0,1)$: a function that is constant and then convex and increasing, with a $C^1$ junction at $\alpha=|1-2c|$, is convex on the whole interval, and this is the form the corner argument uses.
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), p. 30, Appendix, proof of Corollary 1, first paragraph, second sentence

import Mathlib
import Definitions.Def_InfoBargaining_Uniform_Setting

namespace InfoBargaining.Uniform

theorem A_constant_then_convex (c : ℝ) (hc : c ∈ Set.Ioo (0:ℝ) 1) :
    (∀ α ∈ Set.Ioo (0:ℝ) 1, ∀ α' ∈ Set.Ioo (0:ℝ) 1,
        α ≤ |1 - 2 * c| → α' ≤ |1 - 2 * c| → A α c = A α' c) ∧
    StrictMonoOn (fun α => A α c) (Set.Ioo (0:ℝ) 1 ∩ Set.Ici |1 - 2 * c|) ∧
    ConvexOn ℝ (Set.Ioo (0:ℝ) 1) (fun α => A α c) := by sorry

end InfoBargaining.Uniform
