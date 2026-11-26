-- Prove2me | Theorems.Thm_LayeredTransitionAudit_equality_midpoint_width
-- name    : LayeredTransitionAudit.equality_midpoint_width
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T20:58:47.787799+00:00
-- url     : https://prove2.me/theorems/f6192209-77d6-56c8-96c4-2f5cb8fe39c2
-- title:
--   Reading the halves in order requires exponential midpoint width for equality
-- statement:
--   A deterministic layered diagram receives two n-bit strings consecutively, all bits of the first before any bit of the second. Assume its Boolean output always decides whether the two strings are equal. At least 2^n distinct states must be reachable at the midpoint, even if the transition rule can depend on the layer.
-- source:
--   The distinguishable-prefix argument for deterministic automata.

import Definitions.Def_LayeredTransitionAudit

open LayeredTransitionAudit

theorem LayeredTransitionAudit.equality_midpoint_width {Q : Type*} [DecidableEq Q]
    (width : ℕ) (step : ℕ → Q → Bool → Q) (root : Q) (output : Q → Bool)
    (correct : ∀ x y : Fin width → Bool,
      output (run step 0 root (List.ofFn x ++ List.ofFn y)) = decide (x = y)) :
    2^width ≤ (reachable (fun _ => Finset.univ) step root width).card := by sorry
