-- Prove2me | Theorems.Thm_LogStarBinPacking_claim_2_5
-- name    : LogStarBinPacking.claim_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:32:23.462567+00:00
-- url     : https://prove2.me/theorems/28a7530b-2ee4-46c6-831d-4a7790e5098d
-- title:
--   Claim 2.5 — at most $96t$ items outside the type-zero triples
-- statement:
--   Let $I$ be a bin packing instance with $n$ items, $b\ge1$ an integer, $V$ a finite set with $|V|\ge n+b$, $h:V\to[0,1]\cap\mathbb Q$ and $\varepsilon>0$ rational. Let $J$ be the three-item instance of the proof of Lemma 2.1, with sizes $s_J$ and scores $p_1,p_2$, and $M=|V|+b$.
--   Let $t\ge0$ be an integer and $\mathcal B$ a packing of $J$ into $M+t$ bins. Let $\mathcal B^*$ be the set of bins of $\mathcal B$ with exactly three items and type score $0$. Then $|U|=3$ and $p_1(U)=0$ for every $U\in\mathcal B^*$, and
--   $$
--   \Big|J\setminus\bigcup\mathcal B^*\Big|\le96t.
--   $$
--
--   The subfamily $\mathcal B^*$ is computed from $\mathcal B$ by inspecting each bin; the bound is the heart of the decoder.
--
--   Differences from the source:
--   - reading: every packing has a computable subfamily B∗ with the properties → the explicit subfamily of bins with three items and p₁ = 0 (the proof's B∗) has them; reason: the explicit filter is the computation the claim refers to; it gives the existential
--   - encoding: a packing into M + t bins → a published Packing of J into M + t labelled bins, empty bins allowed; reason: the paper's t counts bins, empty ones included (proof: ∑(3 − |U|) = 3t)
--   - encoding: indices 1 ≤ r ≤ f and 1 ≤ j ≤ b of the filler and endpoint items → 0-based indices in Fin f and Fin b; reason: relabelling; the same items and sizes
-- source:
--   I. Doron-Arad, Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin, manuscript (sha256 1d88425d…), Claim 2.5, p.7

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_LogStarBinPacking_ThreeItem

namespace LogStarBinPacking

open OAI.BinPackingGap

/-- **Claim 2.5.** Doron-Arad, *Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin*, manuscript (sha256 1d88425d…), Claim 2.5, p.7.
For `t ∈ ℤ_{≥0}`, every packing `B` of `J` into `M + t` bins has a computable subfamily `B∗`
with `|J ∖ ⋃B∗| ≤ 96t` and `|U| = 3`, `p₁(U) = 0` for every `U ∈ B∗`.

**Formalization Note** `B∗` is computed explicitly, as in the proof: `zeroTypeBins P` is the
set of bins with exactly three items and type score zero. `J ∖ ⋃B∗` is the set of items whose bin
is not in `B∗`. `M = |V| + b`; a packing into `M + t` bins may leave bins empty. The standing
data of Lemma 2.1 are binders. -/
theorem claim_2_5 (I : Instance) (b : ℕ) (hb : 1 ≤ b) (V : Type*) [Fintype V] [DecidableEq V]
    (h : V → ℚ) (h0 : ∀ v, 0 ≤ h v) (h1 : ∀ v, h v ≤ 1) (ε : ℚ) (hε : 0 < ε)
    (hV : I.n + b ≤ Fintype.card V) (t : ℕ)
    (P : Packing (jInstance I V b h ε hε h0 h1) (Fintype.card V + b + t)) :
    (∀ β ∈ zeroTypeBins P,
      (binContent P β).card = 3 ∧ ∑ u ∈ binContent P β, ThreeItem.typeScore u = 0) ∧
    (Finset.univ.filter fun u : JItem I V b => binOf P u ∉ zeroTypeBins P).card ≤ 96 * t := by sorry

end LogStarBinPacking
