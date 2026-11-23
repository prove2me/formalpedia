-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_isClique_range_fractionGraph
-- name    : GroupTheoreticShannonCapacity.isClique_range_fractionGraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:27:51.302663+00:00
-- url     : https://prove2.me/theorems/2c937648-1b4c-497f-96ab-63db7ab45089
-- title:
--   Group Theoretic Shannon Capacity: is Clique range fraction Graph
-- statement:
--   The set {0, 1, ..., q-1} is a clique in E_{p/q}.
--       This gives a lower bound ω(E_{p/q}) ≥ q.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean#L494-L550
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean#L494-L550

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix

theorem GroupTheoreticShannonCapacity.isClique_range_fractionGraph (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q ≤ p) :
    (fractionGraph p q).IsClique ((Finset.range q).image (fun i : ℕ => (i : ZMod p))) := by sorry
