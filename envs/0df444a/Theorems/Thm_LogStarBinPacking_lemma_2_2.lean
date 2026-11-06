-- Prove2me | Theorems.Thm_LogStarBinPacking_lemma_2_2
-- name    : LogStarBinPacking.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:30:19.593279+00:00
-- url     : https://prove2.me/theorems/bc3d22e4-5723-43b3-ad53-069f5a1b1c69
-- title:
--   Lemma 2.2 — five item classes: $M=O(N^4)$ and decoding with $C_0=96$
-- statement:
--   Let $N\ge1$ and let $I$ have five classes of $N$ items each. There is an absolute constant $D$ such that for every fixed rational $\varepsilon>0$ one can construct in polynomial time an instance $J$ of $3M$ items with sizes in $(\frac13-\varepsilon,\frac13+\varepsilon)\cap(\frac14,\frac12)$, where
--   $$
--   M\le D\,N^4,
--   $$
--   such that:
--
--   1. a partition of $I$ into feasible five-tuples implies $\mathrm{OPT}(J)=M$;
--   2. a fractional partition of $I$ into feasible five-tuples implies $\mathrm{LP}(J)=M$;
--   3. for every integer $t\ge0$, a packing of $J$ into $M+t$ bins can be converted in polynomial time into a packing of $I$ into at most $N+C_0t$ bins, where $C_0=96$.
--
--   This specializes Lemma 2.1 to the five-class instances produced by [OAI26].
--
--   Differences from the source:
--   - reading: M = O(N⁴) → M ≤ D·N⁴ with D chosen before ε; reason: the proof of Theorem 1.1 uses D as an absolute constant ("absolute constants a, D", p.17)
--   - encoding: "for every fixed ε > 0" → every rational ε > 0; reason: §2, p.3: "ε > 0 is rational. For fixed real ε > 0, choose a smaller positive rational"; the window only shrinks
--   - encoding: an instance with a specified partition into five classes → a FiveClassRaw (N, [A, B, C, D, E]); I is the concatenation; reason: a machine reads encoded data; same instances
--   - encoding: "in polynomial time" → a Mathlib TM2ComputableInPolyTime machine with a finite alphabet on the binary encodings; reason: the standard Turing-machine model; same reading as the published PackingGapReduction
-- source:
--   I. Doron-Arad, Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin, manuscript (sha256 1d88425d…), Lemma 2.2, p.8

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_LogStarBinPacking_FiveClassRaw

namespace LogStarBinPacking

open OAI.BinPackingGap OAI.BinPackingGames.Foundations.Complexity

/-- **Lemma 2.2 (five item classes).** Doron-Arad, *Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin*, manuscript (sha256 1d88425d…), Lemma 2.2, p.8.
Let `N ≥ 1` be an integer and let `I` have five classes of `N` items each. For every fixed
`ε > 0`, one can construct in polynomial time an instance `J` of `3M` items with sizes in
`(1/3 − ε, 1/3 + ε) ∩ (1/4, 1/2)`, where `M = O(N⁴)`, such that:
(i) a partition of `I` into feasible five-tuples implies `OPT(J) = M`;
(ii) a fractional partition of `I` into feasible five-tuples implies `LP(J) = M`;
(iii) for every integer `t ≥ 0`, a packing of `J` into `M + t` bins can be converted in
polynomial time into a packing of `I` into at most `N + C₀t` bins, where `C₀ = 96`.

**Formalization Note** The input is a `FiveClassRaw` `(N, [A, B, C, D, E])` with
`FiveClassRaw.Valid`; `I` is the concatenation of the classes. `ε` is rational (§2, p.3:
"item sizes are rational and ε > 0 is rational"). The constant `D` of `M ≤ D·N⁴` is chosen
before `ε`; the machines may depend on `ε` ("for every fixed ε"). The reduction outputs
`(M, J)` with `J` raw; the converter of (iii) reads the input and a raw packing of `J`. Both are
Mathlib `TM2ComputableInPolyTime` machines with finite alphabets. `LP` is `individualLP`. -/
theorem lemma_2_2 :
    ∃ D : ℕ, ∀ ε : ℚ, 0 < ε →
    ∃ reduce : FiveClassRaw → RawReductionOutput,
    ∃ comp : Turing.TM2ComputableInPolyTime FiveClassRaw.bits
        BinaryEncoding.rawReductionOutputBits reduce,
      MachineFiniteAlphabet.FiniteAlphabet comp.tm ∧
    ∃ decode : FiveClassRaw × RawPacking → RawPacking,
    ∃ comp' : Turing.TM2ComputableInPolyTime FiveClassRaw.packingBits
        BinaryEncoding.rawPackingBits decode,
      MachineFiniteAlphabet.FiniteAlphabet comp'.tm ∧
      ∀ (y : FiveClassRaw) (hy : y.Valid), ∃ hv : (reduce y).2.Valid,
        (reduce y).2.length = 3 * (reduce y).1 ∧
        (reduce y).1 ≤ D * y.1 ^ 4 ∧
        (∀ i : ((reduce y).2.toInstance hv).Item,
          1 / 3 - ε < ((reduce y).2.toInstance hv).size i ∧
          ((reduce y).2.toInstance hv).size i < 1 / 3 + ε ∧
          1 / 4 < ((reduce y).2.toInstance hv).size i ∧
          ((reduce y).2.toInstance hv).size i < 1 / 2) ∧
        (FiveClassRaw.HasTuplePartition y hy →
          opt ((reduce y).2.toInstance hv) = (reduce y).1) ∧
        (FiveClassRaw.HasFractionalTuplePartition y hy →
          individualLP ((reduce y).2.toInstance hv) = ((reduce y).1 : ℝ)) ∧
        (∀ (t : ℕ) (p : RawPacking), RawPacking.Feasible (reduce y).2 p →
          p.bins = (reduce y).1 + t →
          RawPacking.Feasible (FiveClassRaw.flat y) (decode (y, p)) ∧
            (decode (y, p)).bins ≤ y.1 + 96 * t) := by sorry

end LogStarBinPacking
