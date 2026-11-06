-- Prove2me | Theorems.Thm_LogStarBinPacking_lemma_2_1
-- name    : LogStarBinPacking.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:33:09.083331+00:00
-- url     : https://prove2.me/theorems/f4b57f8d-d47a-450a-aaca-7d161bb72fea
-- title:
--   Lemma 2.1 — the finite-state reduction to three items per bin
-- statement:
--   There is a polynomial-time algorithm that, given a bin packing instance $I$, an integer $b\ge1$, a finite set $V$, a function $h:V\to[0,1]\cap\mathbb Q$ and a rational $\varepsilon>0$ with $|V|\ge|I|+b$, outputs a bin packing instance $J$ of $3M$ items, where $M=|V|+b$, with all sizes in
--   $$
--   \Big(\frac13-\varepsilon,\frac13+\varepsilon\Big)\cap\Big(\frac14,\frac12\Big),
--   $$
--   such that:
--
--   1. if there exists a feasible weight family for $(I,b,V,h)$, then $\mathrm{LP}(J)=M$;
--   2. if there are pairwise disjoint state paths $\pi_1,\dots,\pi_b\in P(I,V,h)$ such that $I(\pi_1),\dots,I(\pi_b)$ is a partition of $I$, then $\mathrm{OPT}(J)=M$;
--   3. given a packing of $J$ into $M+t$ bins, for an integer $t\ge0$, one can construct in polynomial time a packing of $I$ into at most $b+96t$ bins.
--
--   This is the paper's main reduction: it turns additive gaps for arbitrary instances, described by state paths, into gaps for instances with all items near $1/3$.
--
--   **Formalization Note** $\varepsilon$ is part of the input, so one machine serves every $\varepsilon$. The decoder of item 3 is a second machine reading the input and a raw packing of $J$.
--
--   Differences from the source:
--   - encoding: inputs (I, b, V, h, ε) with V a finite set → an FSInput record: I raw, b, the values of h as rationals with V = Fin |V|, ε as a rational; reason: a machine reads encoded data; every finite V is a relabelling of Fin |V|
--   - encoding: "in polynomial time" → a Mathlib TM2ComputableInPolyTime machine with a finite alphabet on the binary encodings; reason: the standard Turing-machine model; same reading as the published PackingGapReduction
--   - generalization: I(π₁), …, I(π_b) is a partition of I → the item sets are pairwise disjoint and cover I; empty blocks allowed; reason: a weaker hypothesis that contains every partition into nonempty blocks; the proof uses only disjointness and covering (∑|V(π_j)| = n + b)
-- source:
--   I. Doron-Arad, Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin, manuscript (sha256 1d88425d…), Lemma 2.1, p.4

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_LogStarBinPacking_StatePath
import Definitions.Def_LogStarBinPacking_FSInput

namespace LogStarBinPacking

open OAI.BinPackingGap OAI.BinPackingGames.Foundations.Complexity

/-- **Lemma 2.1 (finite state reduction).** Doron-Arad, *Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin*, manuscript (sha256 1d88425d…), Lemma 2.1, p.4.
There is a polynomial-time algorithm that, given a bin packing instance `I`, an integer `b ≥ 1`,
a finite set `V`, a function `h : V → [0, 1] ∩ ℚ` and a rational `ε > 0` with `|V| ≥ |I| + b`,
outputs a bin packing instance `J` of `3M` items, where `M = |V| + b`, with sizes in
`(1/3 − ε, 1/3 + ε) ∩ (1/4, 1/2)`, such that:
(i) if there exists a feasible weight family for `(I, b, V, h)`, then `LP(J) = M`;
(ii) if there are pairwise disjoint paths `π₁, …, π_b ∈ P(I, V, h)` such that
`I(π₁), …, I(π_b)` is a partition of `I`, then `OPT(J) = M`;
(iii) given a packing of `J` into `M + t` bins, for an integer `t ≥ 0`, one can construct in
polynomial time a packing of `I` into at most `b + 96t` bins.

**Formalization Note** The input is an `FSInput` record (`I` raw, `b`, the values of `h` with
`V = Fin |V|`, `ε`), with `FSInput.Valid` the lemma's domain; `ε` is part of the input, so one
machine serves every `ε`. The output is `(M, J)` with `J` raw. The decoder of (iii) is a second
machine on the input together with a raw packing of `J`. Both machines are Mathlib
`TM2ComputableInPolyTime` with finite alphabets. `LP` is the published `individualLP`. -/
theorem lemma_2_1 :
    ∃ reduce : FSInput → RawReductionOutput,
    ∃ comp : Turing.TM2ComputableInPolyTime FSInput.bits BinaryEncoding.rawReductionOutputBits reduce,
      MachineFiniteAlphabet.FiniteAlphabet comp.tm ∧
    ∃ decode : FSInput × RawPacking → RawPacking,
    ∃ comp' : Turing.TM2ComputableInPolyTime FSInput.packingBits BinaryEncoding.rawPackingBits decode,
      MachineFiniteAlphabet.FiniteAlphabet comp'.tm ∧
      ∀ (x : FSInput) (hx : x.Valid), ∃ hv : (reduce x).2.Valid,
        (reduce x).1 = x.loads.length + x.b ∧
        (reduce x).2.length = 3 * (reduce x).1 ∧
        (∀ i : ((reduce x).2.toInstance hv).Item,
          1 / 3 - x.epsilon < ((reduce x).2.toInstance hv).size i ∧
          ((reduce x).2.toInstance hv).size i < 1 / 3 + x.epsilon ∧
          1 / 4 < ((reduce x).2.toInstance hv).size i ∧
          ((reduce x).2.toInstance hv).size i < 1 / 2) ∧
        (HasFeasibleWeightFamily (x.source hx) x.b x.load →
          individualLP ((reduce x).2.toInstance hv) = ((reduce x).1 : ℝ)) ∧
        ((∃ π : Fin x.b → StatePath (x.source hx) x.State x.load,
            IsDisjointPathPartition (x.source hx) x.load π) →
          opt ((reduce x).2.toInstance hv) = (reduce x).1) ∧
        (∀ (t : ℕ) (p : RawPacking), RawPacking.Feasible (reduce x).2 p →
          p.bins = (reduce x).1 + t →
          RawPacking.Feasible x.inst (decode (x, p)) ∧ (decode (x, p)).bins ≤ x.b + 96 * t) := by sorry

end LogStarBinPacking
