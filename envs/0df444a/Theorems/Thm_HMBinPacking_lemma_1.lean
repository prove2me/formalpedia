-- Prove2me | Theorems.Thm_HMBinPacking_lemma_1
-- name    : HMBinPacking.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:00:25.637846+00:00
-- url     : https://prove2.me/theorems/b73a7b70-f59a-43c7-a4c9-d78629a3db80
-- title:
--   Lemma 1 — a feasible instance gives an integral point of $K$
-- statement:
--   Let $I$ be a Bin Packing instance and $K$ the polytope of §2 (count constraints and cone constraints over the $d^d$ residues). If $I$ is feasible, then
--   $$
--   K\cap\mathbb Z^D\neq\emptyset ,
--   $$
--   that is, there are integers $z_{r,i}$, $n_r$ such that $((z_r,n_r))_r\in K$.
--
--   This is the forward direction of the ILP formulation: a packing, grouped by the residues of its bin configurations modulo $d$, gives an integral point of $K$.
--
--   Differences from the source:
--   - encoding: K ⊆ R^D and K ∩ Z^D ≠ ∅ → KSet I, a set of families over the d^d residues r : Fin d → Fin d of pairs (z_r, n_r) ∈ ℝ^d × ℝ, and an integral point castPoint I z for z with integer entries; reason: R^D with D = (d+1)d^d written in block coordinates; the same set
--   - reading: abstract: d distinct item sizes; problem box (p.1): d item sizes s_1, …, s_d ∈ Z≥1 with no distinctness → Instance as in the problem box; sizes may repeat and need not be ≤ B; reason: the problem box is the definition; it is the stronger of the two readings
--   - encoding: packed into at most b bins of capacity B, with B, s_i ∈ Z≥1 and a_i, b ∈ Z≥0 → Instance with natural-number fields and 0 < B, 0 < d, 0 < s i; Feasible I: an assignment of the items (i, k), k < a_i, to Fin b with every bin load at most B; reason: a map into Fin b may leave bins empty, which is exactly 'at most b'; the same instances
-- source:
--   Koana, Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2, Lemma 1, p.3

import Mathlib
import Definitions.Def_HMBinPacking_Instance
import Definitions.Def_HMBinPacking_ILP

namespace HMBinPacking

/-- **Lemma 1: a feasible instance gives an integral point of `K`.**
Koana, Kumabe, arXiv:2609.16923v2, Lemma 1, p.3: "If the Bin Packing instance is feasible, then
K ∩ Z^D ≠ ∅."

**Formalization Note.** `K` is `KSet I`, indexed by the `d^d` residues `r : Fin d → Fin d`; a point
of `K ∩ Z^D` is the cast `castPoint I z` of an integer family `z r = (z_r, n_r) ∈ ℤ^d × ℤ`. -/
theorem lemma_1 (I : Instance) (h : Feasible I) :
    ∃ z : (Fin I.d → Fin I.d) → (Fin I.d → ℤ) × ℤ, castPoint I z ∈ KSet I := by sorry

end HMBinPacking
