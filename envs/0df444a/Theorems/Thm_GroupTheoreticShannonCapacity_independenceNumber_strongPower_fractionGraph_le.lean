-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_independenceNumber_strongPower_fractionGraph_le
-- name    : GroupTheoreticShannonCapacity.independenceNumber_strongPower_fractionGraph_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:27:59.632808+00:00
-- url     : https://prove2.me/theorems/657f7cac-155f-4d32-b872-dd415d47bb64
-- title:
--   Group Theoretic Shannon Capacity: independence Number strong Power fraction Graph le
-- statement:
--   Independence number of strong power is bounded by power of clique cover weight.
--   For E_{p/q}^⊠(n+1), the product arcs give a clique cover with weight (p/q)^(n+1).
--   Each vertex (v₁,...,v_{n+1}) is in q^(n+1) product arcs (q choices per coordinate).
--   Each product arc is a clique, so any independent set has at most 1 element per arc.
--   Counting: |S| × q^(n+1) ≤ p^(n+1), so |S| ≤ (p/q)^(n+1).
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean#L575-L840
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean#L575-L840

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix

theorem GroupTheoreticShannonCapacity.independenceNumber_strongPower_fractionGraph_le (p q : ℕ) [NeZero p]
    (hq : 0 < q) (hpq : q ≤ p) (n : ℕ) :
    ((strongPower (fractionGraph p q) (n + 1)).indepNum : ℝ) ≤
    ((p : ℝ) / q) ^ (n + 1) := by sorry
