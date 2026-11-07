-- Prove2me | Theorems.Thm_MinSumClust_lemma_5
-- name    : MinSumClust.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:48:42.323415+00:00
-- url     : https://prove2.me/theorems/43aab922-e44c-4697-95af-a7d5b292fdc2
-- title:
--   Lemma 5 — cluster splitting: every output of Algorithm 1 pays for itself (running-time clause carried by Theorem 2)
-- statement:
--   Let $d$ be a pseudometric on $D$, $(\alpha_i)$ a real vector, $f>0$ and $\gamma\ge 8$, and let $\langle C_{\mathrm{core}},C_{\mathrm{out}}\rangle$ be $\gamma$-splittable. Algorithm 1 repeatedly splits off a block of exactly $2|C_{\mathrm{core}}|$ clients of $C_{\mathrm{out}}$ while more than $2|C_{\mathrm{core}}|$ remain, and puts the rest $C'$ with the core. Then:
--
--   1. for every $C'\subseteq C_{\mathrm{out}}$ with $|C'|\le 2|C_{\mathrm{core}}|$ and every family of pairwise disjoint blocks of size exactly $2|C_{\mathrm{core}}|$ whose union is $C_{\mathrm{out}}\setminus C'$, the cluster $C_1=C_{\mathrm{core}}\cup C'$ and every block $C$ satisfy
--   $$\sum_{i\in C}\alpha_i\ \ge\ f+\mathrm{cost}(C);$$
--   2. such a $C'$ and such blocks exist.
--
--   So $C_{\mathrm{core}}\cup C_{\mathrm{out}}$ is partitioned into clusters $C_1\supseteq C_{\mathrm{core}},C_2,\dots,C_r$ that each pay their opening and connection cost. This is the basic step that turns dual payments into a feasible LMP solution.
--
--   Differences from the source:
--
--   - reading: there exists a polynomial-time algorithm that partitions C into clusters with the dual payment property → every output of Algorithm 1 (every admissible C′ and blocks) has the property, and an output exists; reason: the algorithm is Algorithm 1, whose arbitrary choices give exactly these outputs; its polynomial running time is carried by Theorem 2's polynomial-time clause, whose algorithm runs it
--   - generalization: the guarantee for the output of the algorithm → the guarantee for every possible output of Algorithm 1; reason: it implies the paper's statement for whichever output the algorithm returns
--   - generalization: d is a metric → d is any pseudometric (distinct points may be at distance 0); reason: the argument uses only nonnegativity, symmetry, the zero diagonal and the triangle inequality; every metric is a pseudometric, so the paper's statement is the special case
--   - reading: a dual solution {α_i} → any real vector α; reason: §3, p.16: "any dual solution"
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Lemma 5 and Algorithm 1, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_MinSumClust_cost
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumClust_IsSplittable

namespace MinSumClust

/-- **Lemma 5 (cluster splitting)**, p.17 (PDF p.19).

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Lemma 5 and Algorithm 1, p.17.

Let `γ ≥ 8` and let `⟨C_core, C_out⟩` be γ-splittable. Every output of Algorithm 1 satisfies the
dual payment property: for every `C′ ⊆ C_out` with `|C′| ≤ 2|C_core|` and every family of pairwise
disjoint blocks of size exactly `2|C_core|` whose union is `C_out \ C′`, the cluster
`C₁ = C_core ∪ C′` and every block `C` satisfy `∑_{i ∈ C} α_i ≥ f + cost(C)`; and such a `C′` with
such blocks exists (so the clusters partition `C_core ∪ C_out`, with `C_core ⊆ C₁`).

**Formalization Note.** "There exists a polynomial-time algorithm that … partitions" is read as the
partitions Algorithm 1 outputs (its arbitrary choices give exactly the families above); the running
time of Algorithm 1 is carried by Theorem 2's polynomial-time clause. The distance is any
pseudometric (the paper's `d` is a metric); `α` is any real vector and `f > 0` (§3, p.16). -/
theorem lemma_5 {D : Type*} [DecidableEq D] (d : D → D → ℝ) (hd : IsPseudometric d)
    (α : D → ℝ) (f γ : ℝ) (hf : 0 < f) (hγ : 8 ≤ γ) (Ccore Cout : Finset D)
    (hC : IsSplittable d α f γ Ccore Cout) :
    (∀ C' ⊆ Cout, C'.card ≤ 2 * Ccore.card → ∀ blocks : Finset (Finset D),
        (blocks : Set (Finset D)).PairwiseDisjoint id →
        (∀ B ∈ blocks, B.card = 2 * Ccore.card) → blocks.biUnion id = Cout \ C' →
        f + cost d (Ccore ∪ C') ≤ ∑ i ∈ Ccore ∪ C', α i ∧
          ∀ B ∈ blocks, f + cost d B ≤ ∑ i ∈ B, α i) ∧
      ∃ C' ⊆ Cout, C'.card ≤ 2 * Ccore.card ∧ ∃ blocks : Finset (Finset D),
        (blocks : Set (Finset D)).PairwiseDisjoint id ∧
        (∀ B ∈ blocks, B.card = 2 * Ccore.card) ∧ blocks.biUnion id = Cout \ C' := by sorry

end MinSumClust
