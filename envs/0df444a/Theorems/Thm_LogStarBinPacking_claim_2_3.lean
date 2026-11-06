-- Prove2me | Theorems.Thm_LogStarBinPacking_claim_2_3
-- name    : LogStarBinPacking.claim_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:32:04.331164+00:00
-- url     : https://prove2.me/theorems/d1e462b4-24ee-41eb-ad10-099a05225e7c
-- title:
--   Claim 2.3 — path triples are feasible; disjoint paths give $\mathrm{OPT}(J)=M$
-- statement:
--   Let $I$ be a bin packing instance with $n$ items, $b\ge1$ an integer, $V$ a finite set with $|V|\ge n+b$, $h:V\to[0,1]\cap\mathbb Q$ and $\varepsilon>0$ rational. Let $J$ be the three-item instance of the proof of Lemma 2.1, with sizes $s_J$ and scores $p_1,p_2$, and $M=|V|+b$.
--   Then:
--
--   1. for every state path $\pi\in P(I,V,h)$ and $1\le j\le b$, every member of $T_j(\pi)$ is a feasible triple (three items of total size at most one);
--   2. if $\pi_1,\dots,\pi_b$ are pairwise disjoint state paths whose item sets partition $I$, then
--   $$
--   \mathrm{OPT}(J)=M.
--   $$
--
--   This is the completeness direction of the finite-state reduction.
--
--   Differences from the source:
--   - generalization: I(π₁), …, I(π_b) is a partition of I → the item sets are pairwise disjoint and cover I; empty blocks allowed; reason: a weaker hypothesis that contains every partition into nonempty blocks; the proof uses only disjointness and covering (∑|V(π_j)| = n + b)
--   - encoding: indices 1 ≤ r ≤ f and 1 ≤ j ≤ b of the filler and endpoint items → 0-based indices in Fin f and Fin b; reason: relabelling; the same items and sizes
-- source:
--   I. Doron-Arad, Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin, manuscript (sha256 1d88425d…), Claim 2.3 and (2.9), p.5

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_LogStarBinPacking_StatePath
import Definitions.Def_LogStarBinPacking_ThreeItem

namespace LogStarBinPacking

open OAI.BinPackingGap

/-- **Claim 2.3.** Doron-Arad, *Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin*, manuscript (sha256 1d88425d…), Claim 2.3 and (2.9), p.5.
Every `T_j(π)` consists of feasible triples. Disjoint paths `π₁, …, π_b` whose item sets
partition `I` imply `OPT(J) = M`, where `M = |V| + b`.

**Formalization Note** `T_j(π)` is `pathTriples I b π j` with `j : Fin b` (`0`-based). A
feasible triple is a set of three items of total size (2.5) at most one. "Item sets partition
`I`" is read as: pairwise disjoint and covering `I` (`IsDisjointPathPartition`). The standing
data of Lemma 2.1 are binders. -/
theorem claim_2_3 (I : Instance) (b : ℕ) (hb : 1 ≤ b) (V : Type*) [Fintype V] [DecidableEq V]
    (h : V → ℚ) (h0 : ∀ v, 0 ≤ h v) (h1 : ∀ v, h v ≤ 1) (ε : ℚ) (hε : 0 < ε)
    (hV : I.n + b ≤ Fintype.card V) :
    (∀ (π : StatePath I V h) (j : Fin b), ∀ U ∈ pathTriples I b π j,
      U.card = 3 ∧ ∑ u ∈ U, ThreeItem.size I.size h ε u ≤ 1) ∧
    (∀ π : Fin b → StatePath I V h, IsDisjointPathPartition I h π →
      opt (jInstance I V b h ε hε h0 h1) = Fintype.card V + b) := by sorry

end LogStarBinPacking
