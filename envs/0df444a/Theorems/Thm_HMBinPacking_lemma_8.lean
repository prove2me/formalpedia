-- Prove2me | Theorems.Thm_HMBinPacking_lemma_8
-- name    : HMBinPacking.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:01:53.39299+00:00
-- url     : https://prove2.me/theorems/86180e6a-d1a5-4559-828a-7573bf260f23
-- title:
--   Lemma 8 — strong separation over $K$ in $2^{O(d^3)}(L+\ell)^{O(1)}$ bit operations
-- statement:
--   There is one deterministic algorithm and a constant $c$ such that for every instance $I$ and every query $y\in\mathbb Q^D$ ($D=(d+1)d^d$) of encoding length $\ell$, the algorithm, given $(I,y)$, returns a strong separation answer for $y$ over the polytope $K$ of §2 in at most
--   $$
--   2^{c d^3}(L+\ell)^{c}
--   $$
--   bit operations, with output length at most $(D+L+\ell)^{c}$.
--
--   With Lemma 5 this decides whether $K\cap\mathbb Z^D\neq\emptyset$, which is the proof of Theorem 1.
--
--   Differences from the source:
--   - encoding: running time counted in bit operations; no machine model fixed (footnote 1, p.1) → step count of a Mathlib Turing.TM2ComputableAux Bool Bool (OutputsWithin = Turing.TM2OutputsInTime); reason: a Turing machine simulates a bit-operation algorithm and conversely with polynomial overhead, and every time bound of this mission is a class closed under taking polynomials, so the statement is the same
--   - encoding: instance written in binary; L the binary input length → encodeInstance I (published self-delimiting binary encodeNat of B, d, s, a, b) and L = its length; reason: encodeNat spends 2·size(m)+1 bits on m, so L is the binary input length up to a constant factor; no number is written in unary
--   - encoding: enc(q): total binary encoding length of a rational number or vector, including numerators and denominators; ℓ the encoding length of the query → lengths of the published codes encodeRat q and encVec v; reason: the codes are binary with numerator and denominator, so the lengths agree with the paper's up to constant factors, which polynomial bounds absorb
--   - encoding: (·)^{O(1)} and 2^{O(d³)} bounds → explicit constants: ∃ c before every instance with (·)^c and 2^(c·d^3); for a hypothesis with (·)^{O(1)}, ∀ e first; reason: the O-notation read as one constant uniform over all inputs
--   - encoding: strong separation returns u ∈ Q^n and α ∈ Q, or certifies membership → IsSepAnswer: the output word is [true] (with y ∈ Q) or false :: encVec u ++ encodeRat α (with u⊤x ≤ α on Q and α < u⊤y); reason: the oracle's answer written as a binary word; the two cases are exclusive
--   - reading: abstract: d distinct item sizes; problem box (p.1): d item sizes s_1, …, s_d ∈ Z≥1 with no distinctness → Instance as in the problem box; sizes may repeat and need not be ≤ B; reason: the problem box is the definition; it is the stronger of the two readings
--   - encoding: K ⊆ R^D and queries y ∈ Q^D → KFlat I ⊆ (Fin D → ℝ), the preimage of KSet I under the explicit linear bijection unflatten; reason: the flat coordinates of R^D; the same set
--   - encoding: input (the instance, y) → encodeInstance I ++ encVec y; reason: binary word
--   - reading: u⊤x ≤ α < u⊤y for every x ∈ Q, which for an empty Q, read literally, would not constrain α < u⊤y → IsSepAnswer requires α < u⊤y in every case, also for Q = ∅; reason: the answer has to separate y; the paper's own answer for an empty set, 0⊤x ≤ −1 in the proof of Lemma 7, satisfies it
-- source:
--   Koana, Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2, Lemma 8, p.5

import Mathlib
import Definitions.Def_HMBinPacking_Instance
import Definitions.Def_HMBinPacking_Encoding
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_HMBinPacking_ILP
import Definitions.Def_HMBinPacking_Oracles

namespace HMBinPacking

/-- **Lemma 8: strong separation over `K`.**
Koana, Kumabe, arXiv:2609.16923v2, Lemma 8, p.5: "Strong separation over K takes
2^{O(d³)}(L + ℓ)^{O(1)} bit operations, with output length (D + L + ℓ)^{O(1)}."

There are one Turing machine and one constant `c` such that, for every instance `I` and every query
`y ∈ ℚ^D`, the machine on input `(I, y)` outputs a strong separation answer for `y` over `K` within
`2^(c·d³)·(L + ℓ)^c` steps, of length at most `(D + L + ℓ)^c`, where `D = (d + 1)d^d` and `ℓ` is the
encoding length of `y`.

**Formalization Note.** `K` is taken in the flat coordinates `Fin D → ℝ` (`KFlat`, through the
explicit bijection `unflatten`). The machine is `Turing.TM2ComputableAux Bool Bool` with step count as
time (`OutputsWithin`); the input is `encodeInstance I ++ encVec y`. The machine and `c` come before
every instance, including `d`. -/
theorem lemma_8 :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (c : ℕ),
      ∀ (I : Instance) (y : Fin (D I) → ℚ), ∃ w : List Bool,
        OutputsWithin M (encodeInstance I ++ encVec y) w
          (2 ^ (c * I.d ^ 3) * (inputLength I + (encVec y).length) ^ c) ∧
        IsSepAnswer (KFlat I) y w ∧
        w.length ≤ (D I + inputLength I + (encVec y).length) ^ c := by sorry

end HMBinPacking
