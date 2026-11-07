-- Prove2me | Theorems.Thm_HypercliqueFalse_lemma_4_1_linear_time
-- name    : HypercliqueFalse.lemma_4_1_linear_time
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:33:03.722413+00:00
-- url     : https://prove2.me/theorems/e136d7d3-20a2-4582-83ac-6544e6d0fdac
-- title:
--   Lemma 4.1 (Recursive Step) — the children are computed in linear time
-- statement:
--   Let $h \ge 3$ and $q \in \mathbb N$ be constants. For either reduction of Lemma 4.1 there is a word-RAM program that, given arrays $A, B, C, D, E$ of $T_h$ of size $(N, M, a, b, c)$, writes all its children — the main children $(\bar A^g, \bar B^g, \bar C^g, \bar D^g, \bar E^g)$ for $g \in [q]$ and the correction children $(\bar A^{ij}, \bar B^{ij}, \bar C^{ij}, \bar D^{ij}, \bar E^{ij})$ for $1 \le i < j \le q$ — in time
--   $$
--   O(\text{input size}),
--   $$
--   the constant depending on $h$ and $q$.
--
--   This is the linear-time clause of Lemma 4.1; it bounds the cost of the internal nodes of the recursion in the proof of Theorem 2.1.
--
--   Differences from the source:
--   - reading: word RAM with words of Θ(log n) bits, all integers polynomially bounded (p.4) → SolvedWithin: for every integer-bound exponent κ one program, correct at every word width W ≥ b(⌊log₂ s⌋+1) on every instance of scale s with integers at most s^κ, within C·bound + C steps, the bound in the instance's own dimensions (each at most s); reason: the paper runs subroutines on small blocks of a size-n instance with the size-n word RAM (Lemma 4.2, Lemma 4.3, proof of Theorem 2.1), so hypotheses and conclusions must cover instances smaller than the scale; at dimension = scale this is the plain statement, and every-width correctness is the published machine's convention for Θ(log n)-bit words (the paper's algorithms only add, subtract and multiply polynomially bounded integers)
--   - encoding: "compute in linear time new arrays" → SolvedWithin (recStep h q w) with time bound the length of the input list (N', resp. M', then tInput T); output the concatenated tInput encodings of the children in a fixed order; reason: a word-RAM problem needs an input and an output layout; the encoding lists every entry once
--   - reading: arrays of size (N, M, a, b, c), no bound stated → N'q (resp. M'q), M (resp. N), a, b, c, n ≤ s; reason: with Θ(log s)-bit words an input of size superpolynomial in s cannot be addressed; every instance has such a scale (s = its largest dimension)
--   - encoding: arrays of size (N, M, a, b, c), with N/q (resp. M/q) a size of the children → the quotient N' (resp. M') as one more input cell, before tInput T; reason: the published machine has no division or shift, and on empty arrays (say M = 0) the input is only its header, so no constant-time program could get N' from N'q (the identity N' = N/q is a size of the output, and the cell carries no other information)
--   - generalization: q an integer constant (q ≥ 2 in the recursion) → every q : ℕ; reason: specializes to the paper's q
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Lemma 4.1, p.10; proof, p.11; "recall that q is a constant", p.7

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_HypercliqueFalse_SolvedWithin
import Definitions.Def_HypercliqueFalse_recStep

set_option autoImplicit false

open TrulySubcubicAPSP

namespace HypercliqueFalse

/-- **Lemma 4.1 (Recursive Step), the linear-time clause.** Fischer, *The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Lemma 4.1,
p.10: "Given arrays A, B, C, D, E of size (N, M, a, b, c), we can compute in linear time new arrays
Ā^g, B̄^g, C̄^g, D̄^g, Ē^g for all g ∈ [q] and Ā^{ij}, B̄^{ij}, C̄^{ij}, D̄^{ij}, Ē^{ij} for all
1 ≤ i < j ≤ q"; p.7: "recall that q is a constant".

For every `h ≥ 3`, every `q` and either reduction, one word-RAM program (depending on `h` and
`q`) writes the encodings of all children of `lemma_4_1` in `O(input length)` steps.

**Formalization Note.** `recStep h q true` is the first reduction, `recStep h q false` the second;
the time bound is the length of the input list (`N'`, resp. `M'`, followed by `tInput T`). -/
theorem lemma_4_1_linear_time (h q : ℕ) (hh : 3 ≤ h) (w : Bool) :
    SolvedWithin (recStep h q w) (fun _ x => (((recStep h q w).input x).length : ℝ)) := by sorry

end HypercliqueFalse
