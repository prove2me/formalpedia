-- Prove2me | Theorems.Thm_LogStarBinPacking_proposition_3_1
-- name    : LogStarBinPacking.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:32:31.966208+00:00
-- url     : https://prove2.me/theorems/3b542014-bd47-4691-98ac-5ac2b975a68e
-- title:
--   Proposition 3.1 — the [OAI26] construction at $\rho=1/96$
-- statement:
--   Fix $\rho=1/96$. For every integer $c\ge0$, simple graph $G=(V,E)$ with $n=|V|\ge1$ and $m=|E|\ge1$, and integer $k\in\{0,\dots,n\}$, the algorithm $A$ of [OAI26] on input $(G,k,c)$ produces an integer $N\ge1$ and a bin packing instance $I$ with a partition $I=I_1\,\dot\cup\cdots\dot\cup\,I_5$, where $|I_j|=N$ and all sizes lie in $(1/6,1)$. Let $F=\{U\in H(I):|U\cap I_j|=1\ \forall j\}$. Then:
--
--   1. if $\tau(G)\le k$, then $I$ has a partition into members of $F$;
--   2. if $\mathrm{OPT}(I)\le N+c$, then $\tau(G)\le k+n/96$;
--   3. if $G=K_4$ and $k=2$, there are weights $x_U\ge0$ ($U\in F$) with $\sum_{U\in F:\,i\in U}x_U=1$ for every $i\in I$.
--
--   For every fixed $c$, the construction takes polynomial time. Here $\tau(G)$ is the minimum size of a vertex cover.
--
--   This collects the properties of the five-item construction of [OAI26] that the three-item reduction needs; the paper cites them from [OAI26].
--
--   **Formalization Note** $A$ is the published construction and its output is `fiveClassOutput c (1/96)`; $N$ also equals the published `reductionBinBound`. A member of $F$ is a feasible five-tuple.
--
--   Differences from the source:
--   - reading: a partition I = I₁ ∪̇ ⋯ ∪̇ I₅ (unnamed) → the five published roles x, anchor, global, local, flag; reason: the published integral packing builds every bin from one item per role (integralRoleEquiv) and card_roleCopies gives N items per role
--   - encoding: "A produces N, I and the partition" → fiveClassOutput: the published raw items grouped by role, N = the published bin bound; reason: the published machine emits the same items as one list
--   - encoding: a simple graph with n ≥ 1, m ≥ 1 and k ∈ {0, …, n} → a published GraphReductionInput (vertices Fin n, nonempty ordered duplicate-free edge list, k ≤ n); reason: same inputs; an edge forces n ≥ 1
--   - encoding: τ(G) ≤ k and τ(G) ≤ k + n/96 → a cover C with |C| ≤ k (CoverAtMost), resp. with |C| ≤ k + n/96 in ℝ; reason: τ is the least cover size
--   - encoding: G = K₄ → n = 4 and every pair u < v of vertices is an edge; reason: this is the complete graph on four vertices in every edge-list order of the published graph encoding
--   - encoding: "for every fixed c, the construction takes polynomial time" → for every c a TM2ComputableInPolyTime machine with a finite alphabet from graphBits to the five-class encoding; reason: the standard model, as in the published graphPackingComputation
-- source:
--   I. Doron-Arad, Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin, manuscript (sha256 1d88425d…), Proposition 3.1, p.12

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C014
import Definitions.Def_LogStarBinPacking_FiveClassRaw
import Definitions.Def_LogStarBinPacking_fiveClassOutput

namespace LogStarBinPacking

open OAI.BinPackingGap OAI.BinPackingGames.Foundations.Complexity

/-- **Proposition 3.1 ([OAI26] Theorem 3.1 and Propositions 4.1, 5.1, 6.1).** Doron-Arad, *Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin*, manuscript (sha256 1d88425d…),
Proposition 3.1, p.12. Fix `ρ = 1/96`. For every integer `c ≥ 0`, simple graph `G = (V, E)`
with `n = |V| ≥ 1` and `m = |E| ≥ 1`, and integer `k ∈ {0, …, n}`, the algorithm `A` of
[OAI26] on input `(G, k, c)` produces an integer `N ≥ 1` and a bin packing instance `I` with a
partition `I = I₁ ∪̇ ⋯ ∪̇ I₅`, `|I_j| = N`, all sizes in `(1/6, 1)`. Let
`F = {U ∈ H(I) : |U ∩ I_j| = 1 ∀ j}`. Then: (i) if `τ(G) ≤ k`, `I` has a partition into members
of `F`; (ii) if `OPT(I) ≤ N + c`, then `τ(G) ≤ k + n/96`; (iii) if `G = K₄` and `k = 2`, there
are weights `x_U ≥ 0` (`U ∈ F`) with `∑_{U ∈ F, i ∈ U} x_U = 1` for every `i ∈ I`. For every
fixed `c`, the construction takes polynomial time.

**Formalization Note** `A` is the published [OAI26] construction; its output grouped into the
five classes is `fiveClassOutput c (1/96) x` for `x : GraphReductionInput` (a simple graph on
`Fin n` with a nonempty edge list and `k ≤ n`). The classes `I₁, …, I₅` are the five published
roles. A member of `F` is a feasible five-tuple, so (i) and (iii) are `HasTuplePartition` and
`HasFractionalTuplePartition`. `N` is also `reductionBinBound c (1/96) G k`. `τ(G) ≤ k` is
`CoverAtMost`; `τ(G) ≤ k + n/96` is a cover of real size at most `k + n/96`. `G = K₄` is
`n = 4` with every pair `u < v` an edge, so every edge-list order of the complete graph on four
vertices is covered (the published `completeFourGraph` is one of them). The last sentence is
one `TM2ComputableInPolyTime` machine with a finite alphabet for each `c`, from the published
graph encoding `graphBits`. -/
theorem proposition_3_1 :
    (∀ (c : ℕ) (x : GraphReductionInput), ∃ hy : (fiveClassOutput c (1 / 96) x).Valid,
      (fiveClassOutput c (1 / 96) x).1 = reductionBinBound c (1 / 96) x.graph x.k ∧
      (∀ i : (FiveClassRaw.toInstance (fiveClassOutput c (1 / 96) x) hy).Item,
        1 / 6 < (FiveClassRaw.toInstance (fiveClassOutput c (1 / 96) x) hy).size i ∧
        (FiveClassRaw.toInstance (fiveClassOutput c (1 / 96) x) hy).size i < 1) ∧
      (x.graph.CoverAtMost x.k →
        FiveClassRaw.HasTuplePartition (fiveClassOutput c (1 / 96) x) hy) ∧
      (opt (FiveClassRaw.toInstance (fiveClassOutput c (1 / 96) x) hy) ≤
          (fiveClassOutput c (1 / 96) x).1 + c →
        ∃ C : Finset x.graph.Vertex, x.graph.IsCover C ∧
          (C.card : ℝ) ≤ (x.k : ℝ) + (x.graph.n : ℝ) / 96) ∧
      (x.graph.n = 4 → (∀ u v : x.graph.Vertex, u < v → (u, v) ∈ x.graph.edges) → x.k = 2 →
        FiveClassRaw.HasFractionalTuplePartition (fiveClassOutput c (1 / 96) x) hy)) ∧
    ∀ c : ℕ, ∃ comp : Turing.TM2ComputableInPolyTime graphBits FiveClassRaw.bits
        (fiveClassOutput c (1 / 96)),
      MachineFiniteAlphabet.FiniteAlphabet comp.tm := by sorry

end LogStarBinPacking
