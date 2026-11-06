-- Prove2me | Theorems.Thm_LogStarBinPacking_claim_2_6
-- name    : LogStarBinPacking.claim_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:32:38.446061+00:00
-- url     : https://prove2.me/theorems/85c9131c-ecba-42ce-8199-fc19ae9b7812
-- title:
--   Claim 2.6 — decoding a packing of $J$ in polynomial time
-- statement:
--   Let $(I,b,V,h,\varepsilon)$ be an input of Lemma 2.1 and $J$ the instance of its proof, with $M=|V|+b$. For every integer $t\ge0$, a packing of $J$ into $M+t$ bins yields, in polynomial time, a packing of $I$ into at most
--   $$
--   b+96t
--   $$
--   bins. That is, one polynomial-time algorithm reads the input and a packing of $J$ into $M+t$ bins and outputs a packing of $I$ into at most $b+96t$ bins.
--
--   This is the soundness direction of the reduction: few extra bins for $J$ give few extra bins for $I$.
--
--   **Formalization Note** $J$ is the raw list `FSInput.threeItemRaw`. Packings are raw packings (a bin label per item, every bin of load at most one).
--
--   Differences from the source:
--   - encoding: inputs (I, b, V, h, ε) with V a finite set → an FSInput record: I raw, b, the values of h as rationals with V = Fin |V|, ε as a rational; reason: a machine reads encoded data; every finite V is a relabelling of Fin |V|
--   - encoding: "in polynomial time" → a Mathlib TM2ComputableInPolyTime machine with a finite alphabet on the binary encodings; reason: the standard Turing-machine model; same reading as the published PackingGapReduction
-- source:
--   I. Doron-Arad, Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin, manuscript (sha256 1d88425d…), Claim 2.6, p.7

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_LogStarBinPacking_FSInput

namespace LogStarBinPacking

open OAI.BinPackingGap OAI.BinPackingGames.Foundations.Complexity

/-- **Claim 2.6.** Doron-Arad, *Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin*, manuscript (sha256 1d88425d…), Claim 2.6, p.7.
For `t ∈ ℤ_{≥0}`, a packing of `J` into `M + t` bins yields, in polynomial time, a packing of
`I` into at most `b + 96t` bins.

**Formalization Note** `J` is the instance of the proof of Lemma 2.1 in raw form,
`FSInput.threeItemRaw x`, for the input `x = (I, b, h, ε)` with `V = Fin |V|`. The decoder is a
Mathlib `TM2ComputableInPolyTime` machine with a finite alphabet; it reads `x` and a raw packing
`p` of `J` and outputs a raw packing of `I`. A raw packing is feasible when it assigns every
item a label below its bin count and every bin has load at most one; unused labels are allowed. -/
theorem claim_2_6 :
    ∃ decode : FSInput × RawPacking → RawPacking,
    ∃ comp : Turing.TM2ComputableInPolyTime FSInput.packingBits BinaryEncoding.rawPackingBits decode,
      MachineFiniteAlphabet.FiniteAlphabet comp.tm ∧
      ∀ x : FSInput, x.Valid → ∀ (t : ℕ) (p : RawPacking),
        RawPacking.Feasible x.threeItemRaw.2 p → p.bins = x.threeItemRaw.1 + t →
        RawPacking.Feasible x.inst (decode (x, p)) ∧ (decode (x, p)).bins ≤ x.b + 96 * t := by sorry

end LogStarBinPacking
