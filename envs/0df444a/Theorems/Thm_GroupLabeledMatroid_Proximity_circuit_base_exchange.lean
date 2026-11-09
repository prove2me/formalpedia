-- Prove2me | Theorems.Thm_GroupLabeledMatroid_Proximity_circuit_base_exchange
-- name    : GroupLabeledMatroid.Proximity.circuit_base_exchange
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:22.403676+00:00
-- url     : https://prove2.me/theorems/5e6b9b91-2e50-4993-9a37-7e96a5df3a7f
-- title:
--   Lemma 7 — circuit–base exchange
-- statement:
--   Let $B$ be a base and $C$ a circuit of a finite matroid $M$. For every $b\in B\cap C$ there is an element $a\in C\setminus B$ such that
--
--   $$(B\setminus\{b\})\cup\{a\}\text{ is a base of }M.$$
--
--   This is the circuit–base exchange fact used in the block counting lemmas.
--
--   Differences from the source:
--   - encoding: finite ground set E and finite subsets → Finset subsets of a finite ambient type with classical decidable equality, genuine Mathlib ground M.E, and finite natural ranks; reason: every finite source ground admits this representation; arbitrary subsets M.E support minors; finite rank conversion has no infinite case; classical equality imposes no restriction on the label group
-- source:
--   Siyue Liu, Taihei Oki, Chao Xu, Proximity Theorem and FPT Algorithm for Minimum Group-labeled Matroid Bases, STOC 2027 submission #554 (October 2026), p. 5, Lemma 7

import Mathlib

namespace GroupLabeledMatroid.Proximity

theorem circuit_base_exchange {E : Type*} [Fintype E] [DecidableEq E]
    (M : Matroid E) (B C : Finset E) (hB : M.IsBase (B : Set E))
    (hC : M.IsCircuit (C : Set E)) (b : E) (hb : b ∈ B ∩ C) :
    ∃ a ∈ C \ B, M.IsBase ((insert a (B.erase b) : Finset E) : Set E) := by sorry

end GroupLabeledMatroid.Proximity
