-- Prove2me | Theorems.Thm_GTWSched_NPC_lemma_1_construction
-- name    : GTWSched.NPC.lemma_1_construction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:47:38.467146+00:00
-- url     : https://prove2.me/theorems/5638fbbf-e53d-439d-8c89-44f62dc6e9ee
-- title:
--   Proof of LEMMA 1, p. 333 — the instance EO built from a partition instance Y has a solution iff Y does
-- statement:
--   Let $Y=\{y_1,\dots,y_n\}$ with $n\ge1$ and every $y_i>1$ be an instance of Partition. Define $X=\{x_1,\dots,x_{2n}\}$ by
--   $$x_1=1,\qquad x_{2i}=x_{2i-1}+y_i\ (1\le i\le n),\qquad x_{2i+1}=x_{2i}+1\ (1\le i<n).$$
--   Then
--   1. $X$ is an instance of even-odd partition (positive integers with $x_i<x_{i+1}$ for $1\le i<2n$), and
--   2. $Y$ can be split into two parts of equal sum if and only if $X$ can be split into two parts of equal sum containing exactly one of $x_{2i-1},x_{2i}$ each, for every $i$.
--
--   This is the reduction from Partition to even-odd partition in the proof of LEMMA 1.
--
--   **Formalization Note** $Y$ is a list of natural numbers (`y ≠ []` is $n\ge1$); the paper assumes $y_i>1$ "without loss of generality", and that assumption is a hypothesis here. Partition is the published `ProjSchedTW.Complexity.PartitionYes`, which splits the index set of the list.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 333, proof of LEMMA 1

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_GTWSched_NPC_Schedules
import Definitions.Def_GTWSched_NPC_Problems

namespace GTWSched.NPC

open ProjSchedTW.Complexity

/-- Proof of LEMMA 1, p. 333: for a partition instance `Y = [y₁, …, yₙ]` with `n ≥ 1` and every
`yᵢ > 1`, the list `X` with `x₁ = 1`, `x₂ᵢ = x₂ᵢ₋₁ + yᵢ`, `x₂ᵢ₊₁ = x₂ᵢ + 1` is an even-odd
partition instance, and `Y` has a partition into two parts of equal sum iff `X` has an even-odd
partition into two parts of equal sum. -/
theorem lemma_1_construction (y : List ℕ) (hy : y ≠ []) (hy1 : ∀ v ∈ y, 1 < v) :
    EOInstance (eoOfPartition y) ∧ (PartitionYes y ↔ EOYes (eoOfPartition y)) := by sorry

end GTWSched.NPC
