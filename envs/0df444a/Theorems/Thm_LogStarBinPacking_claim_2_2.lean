-- Prove2me | Theorems.Thm_LogStarBinPacking_claim_2_2
-- name    : LogStarBinPacking.claim_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:31:44.610231+00:00
-- url     : https://prove2.me/theorems/67d0fb96-5b3e-4c9f-a255-d23e1f615a86
-- title:
--   Claim 2.2 — feasible triples have $p_1\le0$; the type-zero patterns (2.8)
-- statement:
--   Let $I$ be a bin packing instance with $n$ items, $b\ge1$ an integer, $V$ a finite set with $|V|\ge n+b$, $h:V\to[0,1]\cap\mathbb Q$ and $\varepsilon>0$ rational. Let $J$ be the three-item instance of the proof of Lemma 2.1, with sizes $s_J$ and scores $p_1,p_2$, and $M=|V|+b$.
--   A triple is a set of three distinct items of $J$, feasible if its total size is at most one. Then:
--
--   1. every feasible triple $U$ has $p_1(U)\le0$;
--   2. a triple $U$ has $p_1(U)=0$ if and only if its class pattern is one of $S^+S^-X$, $S^+S^-X^0$, $S^-E^-_1E^-_2$, $S^+E^+_1E^+_2$;
--   3. a triple with $p_1(U)=0$ is feasible if and only if $p_2(U)\le0$.
--
--   This identifies the intended triples of the reduction among all triples of $J$.
--
--   Differences from the source:
--   - encoding: indices 1 ≤ r ≤ f and 1 ≤ j ≤ b of the filler and endpoint items → 0-based indices in Fin f and Fin b; reason: relabelling; the same items and sizes
-- source:
--   I. Doron-Arad, Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin, manuscript (sha256 1d88425d…), Claim 2.2 and (2.8), p.5

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_LogStarBinPacking_ThreeItem

namespace LogStarBinPacking

open OAI.BinPackingGap

/-- **Claim 2.2.** Doron-Arad, *Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin*, manuscript (sha256 1d88425d…), Claim 2.2 and (2.8), p.5.
Every feasible triple `U` of `J` has `p₁(U) ≤ 0`. The triples with `p₁(U) = 0` have
precisely the patterns `S⁺S⁻X`, `S⁺S⁻X⁰`, `S⁻E⁻₁E⁻₂`, `S⁺E⁺₁E⁺₂` of (2.8); they are feasible
iff `p₂(U) ≤ 0`.

**Formalization Note** A triple is a set of three distinct items of `J`; it is feasible when its
total size (2.5) is at most one. The class pattern of `U` is the multiset of the classes of its
items. The standing data of Lemma 2.1 are binders. -/
theorem claim_2_2 (I : Instance) (b : ℕ) (hb : 1 ≤ b) (V : Type*) [Fintype V] [DecidableEq V]
    (h : V → ℚ) (h0 : ∀ v, 0 ≤ h v) (h1 : ∀ v, h v ≤ 1) (ε : ℚ) (hε : 0 < ε)
    (hV : I.n + b ≤ Fintype.card V) :
    (∀ U : Finset (JItem I V b), U.card = 3 →
      ∑ u ∈ U, ThreeItem.size I.size h ε u ≤ 1 → ∑ u ∈ U, ThreeItem.typeScore u ≤ 0) ∧
    (∀ U : Finset (JItem I V b), U.card = 3 →
      (∑ u ∈ U, ThreeItem.typeScore u = 0 ↔ pattern U ∈ zeroPatterns)) ∧
    (∀ U : Finset (JItem I V b), U.card = 3 → ∑ u ∈ U, ThreeItem.typeScore u = 0 →
      (∑ u ∈ U, ThreeItem.size I.size h ε u ≤ 1 ↔ ∑ u ∈ U, ThreeItem.loadScore I.size h u ≤ 0)) := by sorry

end LogStarBinPacking
