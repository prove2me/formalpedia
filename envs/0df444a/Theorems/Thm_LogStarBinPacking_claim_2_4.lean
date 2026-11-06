-- Prove2me | Theorems.Thm_LogStarBinPacking_claim_2_4
-- name    : LogStarBinPacking.claim_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:31:55.945404+00:00
-- url     : https://prove2.me/theorems/070a716a-7c3d-475d-b152-816f56557ed2
-- title:
--   Claim 2.4 — a feasible weight family gives $\mathrm{LP}(J)=M$
-- statement:
--   Let $I$ be a bin packing instance with $n$ items, $b\ge1$ an integer, $V$ a finite set with $|V|\ge n+b$, $h:V\to[0,1]\cap\mathbb Q$ and $\varepsilon>0$ rational. Let $J$ be the three-item instance of the proof of Lemma 2.1, with sizes $s_J$ and scores $p_1,p_2$, and $M=|V|+b$.
--   If there is a feasible weight family for $(I,b,V,h)$, then the configuration LP of $J$ satisfies
--   $$
--   \mathrm{LP}(J)=M.
--   $$
--   Here $\mathrm{LP}(J)=\min\{\sum_{U\in H(J)}y_U:\ y\ge0,\ \sum_{U\ni u}y_U\ge1\ \forall u\in J\}$ over the configurations $H(J)=\{U\subseteq J:s_J(U)\le1\}$.
--
--   This is the fractional completeness direction, used for the configuration-LP gap.
--
--   Differences from the source:
--   - encoding: LP(J) as a minimum → the published individualLP, the infimum of the same covering LP; reason: the LP is feasible and bounded, so the infimum is the minimum
--   - encoding: indices 1 ≤ r ≤ f and 1 ≤ j ≤ b of the filler and endpoint items → 0-based indices in Fin f and Fin b; reason: relabelling; the same items and sizes
-- source:
--   I. Doron-Arad, Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin, manuscript (sha256 1d88425d…), Claim 2.4, p.6

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_LogStarBinPacking_StatePath
import Definitions.Def_LogStarBinPacking_ThreeItem

namespace LogStarBinPacking

open OAI.BinPackingGap

/-- **Claim 2.4.** Doron-Arad, *Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin*, manuscript (sha256 1d88425d…), Claim 2.4, p.6.
A feasible weight family for `(I, b, V, h)` implies `LP(J) = M`, where `M = |V| + b`.

**Formalization Note** `LP(J)` is the published `individualLP`: the infimum of `∑ y_U` over
`y ≥ 0` on the configurations `U ∈ H(J)` with `∑_{U ∋ u} y_U ≥ 1` for every item `u` (p.2).
A feasible weight family is (2.2) with real weights. The standing data of Lemma 2.1 are binders. -/
theorem claim_2_4 (I : Instance) (b : ℕ) (hb : 1 ≤ b) (V : Type*) [Fintype V] [DecidableEq V]
    (h : V → ℚ) (h0 : ∀ v, 0 ≤ h v) (h1 : ∀ v, h v ≤ 1) (ε : ℚ) (hε : 0 < ε)
    (hV : I.n + b ≤ Fintype.card V) (hx : HasFeasibleWeightFamily I b h) :
    individualLP (jInstance I V b h ε hε h0 h1) = ((Fintype.card V + b : ℕ) : ℝ) := by sorry

end LogStarBinPacking
