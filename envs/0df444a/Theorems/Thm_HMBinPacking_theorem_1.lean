-- Prove2me | Theorems.Thm_HMBinPacking_theorem_1
-- name    : HMBinPacking.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:00:26.094201+00:00
-- url     : https://prove2.me/theorems/a3306300-69fc-4a59-bb40-1ae4193769b3
-- title:
--   Theorem 1 — Bin Packing is decided deterministically in $O^*(2^{d^{O(d)}})$ time
-- statement:
--   There are one deterministic algorithm and a constant $c$ such that for every Bin Packing instance $I=(B,d,s,a,b)$ — every $d\ge1$, $B\ge1$, sizes $s_i\ge1$, multiplicities $a_i\ge0$ and bin bound $b\ge0$, with all numbers written in binary — the algorithm decides whether $I$ is feasible in at most
--   $$
--   2^{d^{c d}}\cdot L^{c}
--   $$
--   bit operations, where $L$ is the binary input length. In other words, Bin Packing can be decided deterministically in $O^*(2^{d^{O(d)}})$ time, and is fixed-parameter tractable in the number $d$ of item sizes.
--
--   The algorithm and the constant are the same for every $d$: a bound of the form $L^{f(d)}$, or a different algorithm for each $d$, would not be this theorem. The algorithm answers both "feasible" and "infeasible".
--
--   Differences from the source:
--   - encoding: running time counted in bit operations; no machine model fixed (footnote 1, p.1) → step count of a Mathlib Turing.TM2ComputableAux Bool Bool (OutputsWithin = Turing.TM2OutputsInTime); reason: a Turing machine simulates a bit-operation algorithm and conversely with polynomial overhead, and every time bound of this mission is a class closed under taking polynomials, so the statement is the same
--   - encoding: instance written in binary; L the binary input length → encodeInstance I (published self-delimiting binary encodeNat of B, d, s, a, b) and L = its length; reason: encodeNat spends 2·size(m)+1 bits on m, so L is the binary input length up to a constant factor; no number is written in unary
--   - encoding: O*(2^{d^{O(d)}}) with the polynomial's exponent independent of d → ∃ c, chosen before every instance (including d), with bound 2^(d^(c·d)) · L^c; reason: L ≥ 5 absorbs a multiplicative constant and small d contribute constants, so the classes coincide
--   - encoding: decided (a yes/no answer) → output [true] when Feasible I and [false] otherwise, both within the bound; reason: Boolean output word of the machine; a two-sided decision
--   - reading: abstract: d distinct item sizes; problem box (p.1): d item sizes s_1, …, s_d ∈ Z≥1 with no distinctness → Instance as in the problem box; sizes may repeat and need not be ≤ B; reason: the problem box is the definition; it is the stronger of the two readings
--   - encoding: packed into at most b bins of capacity B, with B, s_i ∈ Z≥1 and a_i, b ∈ Z≥0 → Instance with natural-number fields and 0 < B, 0 < d, 0 < s i; Feasible I: an assignment of the items (i, k), k < a_i, to Fin b with every bin load at most B; reason: a map into Fin b may leave bins empty, which is exactly 'at most b'; the same instances
-- source:
--   Koana, Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2, Theorem 1 and footnote 1, p.1

import Mathlib
import Definitions.Def_HMBinPacking_Instance
import Definitions.Def_HMBinPacking_Encoding
import Definitions.Def_HMBinPacking_OutputsWithin

namespace HMBinPacking

/-- **Theorem 1: Bin Packing is decided deterministically in `O*(2^{d^{O(d)}})` time.**
Koana, Kumabe, *High-Multiplicity Bin Packing is FPT*, arXiv:2609.16923v2, Theorem 1, p.1:
"Bin Packing can be decided deterministically in O∗(2^{d^{O(d)}}) time." Footnote 1, p.1: "Running
times count bit operations; O∗(·) suppresses factors polynomial in the binary input length, with
exponent independent of d."

There are one Turing machine `M` and one constant `c` such that, for every instance `I` (every
`d ≥ 1`, every `B`, `sᵢ ≥ 1`, `aᵢ`, `b`), `M` started on the binary code of `I` outputs `[true]` if
`I` is feasible and `[false]` if it is not, within `2^(d^(c·d)) · L^c` steps, where `L` is the binary
input length.

**Formalization Note.** The machine is Mathlib's `Turing.TM2ComputableAux Bool Bool` and time is
its step count (`OutputsWithin`); the class `{2^(d^(c·d))·L^c}` is closed under polynomials, so this
equals the bit-operation bound. The instance is written in binary (`encodeInstance`). `O(·)` is the
explicit `∃ c`, chosen before every instance, including `d`; no multiplicative constant is needed
since `L ≥ 5`. -/
theorem theorem_1 :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (c : ℕ), ∀ I : Instance,
      (Feasible I →
        OutputsWithin M (encodeInstance I) [true] (2 ^ (I.d ^ (c * I.d)) * inputLength I ^ c)) ∧
      (¬ Feasible I →
        OutputsWithin M (encodeInstance I) [false] (2 ^ (I.d ^ (c * I.d)) * inputLength I ^ c)) := by sorry

end HMBinPacking
