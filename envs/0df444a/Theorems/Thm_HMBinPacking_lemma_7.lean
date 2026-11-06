-- Prove2me | Theorems.Thm_HMBinPacking_lemma_7
-- name    : HMBinPacking.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:01:38.223616+00:00
-- url     : https://prove2.me/theorems/0f6f2093-661d-45c4-ba6b-d9429a467baf
-- title:
--   Lemma 7 — strong separation over $P_r$ in $2^{O(d^3)}(L+\ell)^{O(1)}$ bit operations
-- statement:
--   There is one deterministic algorithm and a constant $c$ such that for every instance $I$, every residue $r\in\{0,\dots,d-1\}^d$ and every query $y\in\mathbb Q^d$ of encoding length $\ell$, the algorithm, given $(I,r,y)$, returns a strong separation answer for $y$ over $P_r=\mathrm{conv}(S_r)$ in at most
--   $$
--   2^{c d^3}(L+\ell)^{c}
--   $$
--   bit operations, with output length at most $(d+L+\ell)^{c}$.
--
--   The case $S_r=\emptyset$ (so $P_r=\emptyset$, answered by $0^\top x\le-1$) is included. Lemma 8 combines these oracles into an oracle for $K$.
--
--   Differences from the source:
--   - encoding: running time counted in bit operations; no machine model fixed (footnote 1, p.1) → step count of a Mathlib Turing.TM2ComputableAux Bool Bool (OutputsWithin = Turing.TM2OutputsInTime); reason: a Turing machine simulates a bit-operation algorithm and conversely with polynomial overhead, and every time bound of this mission is a class closed under taking polynomials, so the statement is the same
--   - encoding: instance written in binary; L the binary input length → encodeInstance I (published self-delimiting binary encodeNat of B, d, s, a, b) and L = its length; reason: encodeNat spends 2·size(m)+1 bits on m, so L is the binary input length up to a constant factor; no number is written in unary
--   - encoding: enc(q): total binary encoding length of a rational number or vector, including numerators and denominators; ℓ the encoding length of the query → lengths of the published codes encodeRat q and encVec v; reason: the codes are binary with numerator and denominator, so the lengths agree with the paper's up to constant factors, which polynomial bounds absorb
--   - encoding: (·)^{O(1)} and 2^{O(d³)} bounds → explicit constants: ∃ c before every instance with (·)^c and 2^(c·d^3); for a hypothesis with (·)^{O(1)}, ∀ e first; reason: the O-notation read as one constant uniform over all inputs
--   - encoding: strong separation returns u ∈ Q^n and α ∈ Q, or certifies membership → IsSepAnswer: the output word is [true] (with y ∈ Q) or false :: encVec u ++ encodeRat α (with u⊤x ≤ α on Q and α < u⊤y); reason: the oracle's answer written as a binary word; the two cases are exclusive
--   - reading: abstract: d distinct item sizes; problem box (p.1): d item sizes s_1, …, s_d ∈ Z≥1 with no distinctness → Instance as in the problem box; sizes may repeat and need not be ≤ B; reason: the problem box is the definition; it is the stronger of the two readings
--   - encoding: input (the instance, r, y) → encodeInstance I ++ encodeResidue r ++ encVec y; reason: binary word
--   - reading: u⊤x ≤ α < u⊤y for every x ∈ Q, which for an empty Q, read literally, would not constrain α < u⊤y → IsSepAnswer requires α < u⊤y in every case, also for Q = ∅; reason: the answer has to separate y; the paper's own answer for an empty set, 0⊤x ≤ −1 in the proof of Lemma 7, satisfies it
-- source:
--   Koana, Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2, Lemma 7, p.5

import Mathlib
import Definitions.Def_HMBinPacking_Instance
import Definitions.Def_HMBinPacking_Encoding
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_HMBinPacking_ILP
import Definitions.Def_HMBinPacking_Oracles

namespace HMBinPacking

/-- **Lemma 7: strong separation over `P_r`.**
Koana, Kumabe, arXiv:2609.16923v2, Lemma 7, p.5: "For every r, strong separation over P_r takes
2^{O(d³)}(L+ℓ)^{O(1)} bit operations, with output length (d + L + ℓ)^{O(1)}."

There are one Turing machine and one constant `c` such that, for every instance `I`, every residue
`r` and every query `y ∈ ℚ^d`, the machine on input `(I, r, y)` outputs a strong separation answer
for `y` over `P_r` within `2^(c·d³)·(L + ℓ)^c` steps, of length at most `(d + L + ℓ)^c`, where `ℓ`
is the encoding length of `y`.

**Formalization Note.** The machine is `Turing.TM2ComputableAux Bool Bool` with step count as time
(`OutputsWithin`); the input is `encodeInstance I ++ encodeResidue r ++ encVec y`. The machine and
`c` come before every instance (including `d`) and every `r`. The case `S_r = ∅` (`P_r = ∅`) is
included. -/
theorem lemma_7 :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (c : ℕ),
      ∀ (I : Instance) (r : Fin I.d → Fin I.d) (y : Fin I.d → ℚ), ∃ w : List Bool,
        OutputsWithin M (encodeInstance I ++ encodeResidue r ++ encVec y) w
          (2 ^ (c * I.d ^ 3) * (inputLength I + (encVec y).length) ^ c) ∧
        IsSepAnswer (Pr I r) y w ∧
        w.length ≤ (I.d + inputLength I + (encVec y).length) ^ c := by sorry

end HMBinPacking
