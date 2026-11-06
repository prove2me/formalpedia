-- Prove2me | Theorems.Thm_HMBinPacking_lemma_4
-- name    : HMBinPacking.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:00:27.291835+00:00
-- url     : https://prove2.me/theorems/48dbf2ae-28ab-4716-abe6-d35de09b3647
-- title:
--   Lemma 4 — an integral point of $K$ gives a feasible packing
-- statement:
--   Let $I$ be a Bin Packing instance and $K$ the polytope of §2. If
--   $$
--   K\cap\mathbb Z^D\neq\emptyset ,
--   $$
--   that is, there are integers $z_{r,i}$, $n_r$ with $((z_r,n_r))_r\in K$, then $I$ is feasible.
--
--   With Lemma 1, the instance is feasible exactly when the ILP has a solution. The point must be integral: a real point of $K$ does not suffice.
--
--   Differences from the source:
--   - encoding: K ⊆ R^D and K ∩ Z^D ≠ ∅ → KSet I, a set of families over the d^d residues r : Fin d → Fin d of pairs (z_r, n_r) ∈ ℝ^d × ℝ, and an integral point castPoint I z for z with integer entries; reason: R^D with D = (d+1)d^d written in block coordinates; the same set
--   - reading: abstract: d distinct item sizes; problem box (p.1): d item sizes s_1, …, s_d ∈ Z≥1 with no distinctness → Instance as in the problem box; sizes may repeat and need not be ≤ B; reason: the problem box is the definition; it is the stronger of the two readings
--   - encoding: packed into at most b bins of capacity B, with B, s_i ∈ Z≥1 and a_i, b ∈ Z≥0 → Instance with natural-number fields and 0 < B, 0 < d, 0 < s i; Feasible I: an assignment of the items (i, k), k < a_i, to Fin b with every bin load at most B; reason: a map into Fin b may leave bins empty, which is exactly 'at most b'; the same instances
-- source:
--   Koana, Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2, Lemma 4, p.4

import Mathlib
import Definitions.Def_HMBinPacking_Instance
import Definitions.Def_HMBinPacking_ILP

namespace HMBinPacking

/-- **Lemma 4: an integral point of `K` gives a feasible packing.**
Koana, Kumabe, arXiv:2609.16923v2, Lemma 4, p.4: "If K ∩ Z^D ≠ ∅, then the Bin Packing instance is
feasible."

**Formalization Note.** `K` is `KSet I`; a point of `K ∩ Z^D` is the cast `castPoint I z` of an
integer family `z r = (z_r, n_r) ∈ ℤ^d × ℤ` (not a point of the real relaxation). -/
theorem lemma_4 (I : Instance)
    (h : ∃ z : (Fin I.d → Fin I.d) → (Fin I.d → ℤ) × ℤ, castPoint I z ∈ KSet I) :
    Feasible I := by sorry

end HMBinPacking
