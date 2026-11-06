-- Prove2me | Theorems.Thm_HMBinPacking_lemma_7_lenstra_step
-- name    : HMBinPacking.lemma_7_lenstra_step
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:00:27.040447+00:00
-- url     : https://prove2.me/theorems/7f40d001-74a3-431c-b123-9a395802798a
-- title:
--   Proof of Lemma 7 — Lenstra's algorithm solves strong optimization over $P_r$
-- statement:
--   Let $I$ be an instance and $r\in\{0,\dots,d-1\}^d$ a residue with $s^\top r\le B$. Then $r\in S_r$, and for every $u\in\mathbb Q^d$,
--   $$
--   \max_{x\in P_r}u^\top x=\max\{u^\top(r+dy): y\in\mathbb Z^d_{\ge0},\ s^\top(r+dy)\le B\},
--   $$
--   and one deterministic algorithm, given $(I,r,u)$, returns an optimal $y^*\in\mathbb Z^d_{\ge0}$ of the right-hand integer program in $2^{c d^3}(L+\mathrm{enc}(u))^{c}$ bit operations, for a constant $c$ independent of the instance; the point $r+dy^*$ lies in $P_r$ and maximizes $u^\top x$ over $P_r$, so returning it solves strong optimization over $P_r$.
--
--   The integer program is bounded (it has finitely many feasible $y$), and after clearing denominators ($qu=w$ with $q>0$ and $w$ integral) its data $(d,s,B,r,w)$ have encoding length at most $(d+L+\mathrm{enc}(u))^{c}$.
--
--   This step, which the paper proves with Lenstra's algorithm [Len83], is the optimization oracle that Lemma 7 turns into a separation oracle.
--
--   Differences from the source:
--   - encoding: running time counted in bit operations; no machine model fixed (footnote 1, p.1) → step count of a Mathlib Turing.TM2ComputableAux Bool Bool (OutputsWithin = Turing.TM2OutputsInTime); reason: a Turing machine simulates a bit-operation algorithm and conversely with polynomial overhead, and every time bound of this mission is a class closed under taking polynomials, so the statement is the same
--   - encoding: instance written in binary; L the binary input length → encodeInstance I (published self-delimiting binary encodeNat of B, d, s, a, b) and L = its length; reason: encodeNat spends 2·size(m)+1 bits on m, so L is the binary input length up to a constant factor; no number is written in unary
--   - encoding: enc(q): total binary encoding length of a rational number or vector, including numerators and denominators; ℓ the encoding length of the query → lengths of the published codes encodeRat q and encVec v; reason: the codes are binary with numerator and denominator, so the lengths agree with the paper's up to constant factors, which polynomial bounds absorb
--   - encoding: (·)^{O(1)} and 2^{O(d³)} bounds → explicit constants: ∃ c before every instance with (·)^c and 2^(c·d^3); for a hypothesis with (·)^{O(1)}, ∀ e first; reason: the O-notation read as one constant uniform over all inputs
--   - reading: abstract: d distinct item sizes; problem box (p.1): d item sizes s_1, …, s_d ∈ Z≥1 with no distinctness → Instance as in the problem box; sizes may repeat and need not be ≤ B; reason: the problem box is the definition; it is the stronger of the two readings
--   - encoding: max_{x∈P_r} u⊤x = max{u⊤(r+dy) : y ∈ Z^d_≥0, s⊤(r+dy) ≤ B} and 'returns an optimal integer vector y*' → the output y* : Fin d → ℕ is feasible, r + dy* ∈ P_r, and u⊤(r+dy*) is the greatest element both of u⊤P_r and of the values of the integer program (IsGreatest twice); reason: both maxima exist and equal the value at the returned point, which is the displayed identity together with the optimality of y*
--   - encoding: input (the instance, r, u) → encodeInstance I ++ encodeResidue r ++ encVec u; output encodeNatVec y*; reason: binary words
--   - encoding: 'Otherwise', the case of the proof of Lemma 7 that is not s⊤r > B, for a residue r → hypothesis ∑ i, s i * r i ≤ B, with r : Fin d → Fin d; reason: this is the case the quoted passage treats; the case s⊤r > B is answered directly in Lemma 7
--   - encoding: after clearing denominators, a bounded integer program with d variables and encoding length polynomial in d + L + enc(u) → the feasible set of y is finite, and some q > 0 and integer vector w with q·u = w give code length of (d, s, B, r, w) at most (d + L + enc(u))^c; reason: the program's data are the integer objective w and the instance's d, s, B, r; u and w = q·u have the same maximizers
-- source:
--   Koana, Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2, Proof of Lemma 7, p.5

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_HMBinPacking_Instance
import Definitions.Def_HMBinPacking_Encoding
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_HMBinPacking_ILP
open ExponomialAssortment.FPTAS (encodeNat)

namespace HMBinPacking

/-- **Proof of Lemma 7: Lenstra's algorithm solves strong optimization over `P_r`.**
Koana, Kumabe, arXiv:2609.16923v2, Proof of Lemma 7, p.5: "Otherwise, r ∈ S_r, and for every
u ∈ Q^d we have max_{x∈P_r} u⊤x = max{u⊤(r + dy) : y ∈ Z^d_≥0, s⊤(r + dy) ≤ B}. After clearing
denominators, the right-hand side is a bounded integer program with d variables and encoding length
polynomial in d + L + enc(u). Lenstra’s algorithm [Len83] returns an optimal integer vector y∗ in
2^{O(d³)}(L + enc(u))^{O(1)} bit operations. Returning r + dy∗ therefore solves strong optimization
over P_r."

There are one Turing machine and one constant `c` such that, for every instance and every residue
`r` with `s⊤r ≤ B`: `r ∈ S_r`; the integer program has finitely many feasible `y`; and for every
`u ∈ ℚ^d`, clearing denominators (`q·u = w` with `q > 0`, `w` integral) gives a program whose data
`(d, s, B, r, w)` have code length at most `(d + L + enc(u))^c`, and the machine on input `(I, r, u)`
outputs, within `2^(c·d³)·(L + enc(u))^c` steps, a vector `y* ∈ ℤ^d_≥0` with `s⊤(r + dy*) ≤ B` such that `r + dy*`
lies in `P_r` and maximizes `u⊤x` over `P_r`, and `y*` maximizes `u⊤(r + dy)` over the integer
program; in particular both maxima of the displayed identity exist and are equal.

**Formalization Note.** The machine is `Turing.TM2ComputableAux Bool Bool` with step count as time
(`OutputsWithin`). The input is `encodeInstance I ++ encodeResidue r ++ encVec u`; the output is the
binary code of `y*`. `enc(u)` is `(encVec u).length`. The machine and `c` come before every
instance, including `d`. `r : Fin d → Fin d` is a residue in `{0, …, d − 1}^d`. -/
theorem lemma_7_lenstra_step :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (c : ℕ),
      ∀ (I : Instance) (r : Fin I.d → Fin I.d), ∑ i, I.s i * (r i : ℕ) ≤ I.B →
      (fun i => ((r i : ℕ) : ℤ)) ∈ Sr I r ∧
      {y' : Fin I.d → ℕ | ∑ i, I.s i * ((r i : ℕ) + I.d * y' i) ≤ I.B}.Finite ∧
      ∀ u : Fin I.d → ℚ,
      (∃ (q : ℕ) (w : Fin I.d → ℤ), 0 < q ∧ (∀ i, (q : ℚ) * u i = (w i : ℚ)) ∧
        (encodeNat I.d ++ encodeNatVec I.s ++ encodeNat I.B ++ encodeResidue r ++
          encodeIntVec w).length ≤ (I.d + inputLength I + (encVec u).length) ^ c) ∧
      ∃ y : Fin I.d → ℕ,
        OutputsWithin M (encodeInstance I ++ encodeResidue r ++ encVec u) (encodeNatVec y)
          (2 ^ (c * I.d ^ 3) * (inputLength I + (encVec u).length) ^ c) ∧
        ∑ i, I.s i * ((r i : ℕ) + I.d * y i) ≤ I.B ∧
        (fun i => (((r i : ℕ) + I.d * y i : ℕ) : ℝ)) ∈ Pr I r ∧
        IsGreatest ((fun x : Fin I.d → ℝ => ∑ i, (u i : ℝ) * x i) '' Pr I r)
          (∑ i, (u i : ℝ) * (((r i : ℕ) + I.d * y i : ℕ) : ℝ)) ∧
        IsGreatest ((fun y' : Fin I.d → ℕ => ∑ i, (u i : ℝ) * (((r i : ℕ) + I.d * y' i : ℕ) : ℝ)) ''
            {y' | ∑ i, I.s i * ((r i : ℕ) + I.d * y' i) ≤ I.B})
          (∑ i, (u i : ℝ) * (((r i : ℕ) + I.d * y i : ℕ) : ℝ)) := by sorry

end HMBinPacking
