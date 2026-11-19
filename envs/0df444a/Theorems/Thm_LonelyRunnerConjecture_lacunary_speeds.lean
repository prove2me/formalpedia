-- Prove2me | Theorems.Thm_LonelyRunnerConjecture_lacunary_speeds
-- name    : LonelyRunnerConjecture.lacunary_speeds
-- status  : Open
-- author  : @LG
-- created : 2026-11-17T01:12:53.938109+00:00
-- url     : https://prove2.me/theorems/6566f011-8e71-4dee-b859-58ab405b2ad2
-- title:
--   Lacunary speeds: $v_{i+1}\ge 2v_i$
-- statement:
--   For $k\ge2$ and $k$ positive integer speeds in which each speed is at least twice the previous one (when sorted), there is a time $t$ with $\|tv\|\ge\frac{1}{k+1}$ for every speed. The conjecture thus holds for geometrically growing (lacunary) speeds with ratio at least $2$.
--
--   **Formalization Note** The hypothesis is written for all pairs `a < b → 2*a ≤ b`, which for a sorted set is equivalent to consecutive doubling $v_{i+1}\ge2v_i$.
-- source:
--   G. Perarnau, O. Serra, The Lonely Runner Conjecture turns 60, https://arxiv.org/abs/2409.20160, Theorem 18 (Barajas–Serra, On the chromatic number of circulant graphs, 2009).

import Mathlib
import Definitions.Def_LonelyRunnerConjecture_Defs

namespace LonelyRunnerConjecture

theorem lacunary_speeds (k : ℕ) (hk : 2 ≤ k) (S : Finset ℕ) (hS : S.card = k)
    (hpos : ∀ v ∈ S, 0 < v)
    (hdoub : ∀ a ∈ S, ∀ b ∈ S, a < b → 2 * a ≤ b) :
    ∃ t : ℝ, ∀ v ∈ S, (1 : ℝ) / (k + 1 : ℝ) ≤ distToNearestInt (t * (v : ℝ)) := by sorry

end LonelyRunnerConjecture
