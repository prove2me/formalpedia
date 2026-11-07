-- Prove2me | Theorems.Thm_MinSumClust_lemma_7
-- name    : MinSumClust.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:49:29.4305+00:00
-- url     : https://prove2.me/theorems/2c583c70-b478-4295-b53d-0033f8f3acdb
-- title:
--   Lemma 7 — cluster editing: every output of the modified Algorithm 1 pays for itself (running-time clause carried by Theorem 2)
-- statement:
--   Let $d$ be a pseudometric, $\alpha$ a real vector, $f>0$ and $\gamma\ge 20$, and let $\langle C_{\mathrm{core}},C_{\mathrm{del}},C_{\mathrm{ins}},C_{\mathrm{out}}\rangle$ be $\gamma$-editable. Run Algorithm 1 with the modified output $C_1=(C_{\mathrm{core}}\setminus C_{\mathrm{del}})\cup C'\cup C_{\mathrm{ins}}$ (proof of Lemma 7). Then:
--
--   1. for every $C'\subseteq C_{\mathrm{out}}$ with $|C'|\le 2|C_{\mathrm{core}}|$ and every family of pairwise disjoint blocks of size exactly $2|C_{\mathrm{core}}|$ whose union is $C_{\mathrm{out}}\setminus C'$, the cluster $C_1$ and every block $C$ satisfy
--   $$\sum_{i\in C}\alpha_i\ \ge\ f+\mathrm{cost}(C);$$
--   2. such a $C'$ and such blocks exist.
--
--   Thus $(C_{\mathrm{core}}\setminus C_{\mathrm{del}})\cup C_{\mathrm{ins}}\cup C_{\mathrm{out}}$ is partitioned into self-paying clusters with $(C_{\mathrm{core}}\setminus C_{\mathrm{del}})\cup C_{\mathrm{ins}}\subseteq C_1$. Combined with Lemma 16 this gives the LMP solution of Theorem 2.
--
--   Differences from the source:
--
--   - reading: there exists a polynomial-time algorithm that partitions C into clusters with the dual payment property → every output of Algorithm 1 with output C₁ = (C_core \ C_del) ∪ C′ ∪ C_ins has the property, and an output exists; reason: the algorithm is the one of the proof of Lemma 7; its polynomial running time is carried by Theorem 2's polynomial-time clause
--   - generalization: the guarantee for the output of the algorithm → the guarantee for every possible output; reason: it implies the paper's statement for whichever output the algorithm returns
--   - generalization: d is a metric → d is any pseudometric (distinct points may be at distance 0); reason: the argument uses only nonnegativity, symmetry, the zero diagonal and the triangle inequality; every metric is a pseudometric, so the paper's statement is the special case
--   - reading: a dual solution {α_i} → any real vector α; reason: §3, p.16: "any dual solution"
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Lemma 7, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_MinSumClust_cost
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumClust_IsEditable

namespace MinSumClust

/-- **Lemma 7 (cluster editing)**, p.18 (PDF p.20).

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Lemma 7, p.18, with the algorithm of its proof (Algorithm 1
with output `C₁ ← (C_core \ C_del) ∪ C′ ∪ C_ins`).

Let `γ ≥ 20` and let `⟨C_core, C_del, C_ins, C_out⟩` be γ-editable. For every `C′ ⊆ C_out` with
`|C′| ≤ 2|C_core|` and every family of pairwise disjoint blocks of size exactly `2|C_core|` whose
union is `C_out \ C′`, the cluster `C₁ = (C_core \ C_del) ∪ C′ ∪ C_ins` and every block `C` satisfy
`∑_{i ∈ C} α_i ≥ f + cost(C)`; and such a `C′` with such blocks exists.

**Formalization Note.** As Lemma 5: every output of the algorithm, plus existence; the running time
is carried by Theorem 2. Pseudometric `d`, any real `α`, `f > 0`. -/
theorem lemma_7 {D : Type*} [DecidableEq D] (d : D → D → ℝ) (hd : IsPseudometric d)
    (α : D → ℝ) (f γ : ℝ) (hf : 0 < f) (hγ : 20 ≤ γ) (Ccore Cdel Cins Cout : Finset D)
    (hC : IsEditable d α f γ Ccore Cdel Cins Cout) :
    (∀ C' ⊆ Cout, C'.card ≤ 2 * Ccore.card → ∀ blocks : Finset (Finset D),
        (blocks : Set (Finset D)).PairwiseDisjoint id →
        (∀ B ∈ blocks, B.card = 2 * Ccore.card) → blocks.biUnion id = Cout \ C' →
        f + cost d ((Ccore \ Cdel) ∪ C' ∪ Cins) ≤ ∑ i ∈ (Ccore \ Cdel) ∪ C' ∪ Cins, α i ∧
          ∀ B ∈ blocks, f + cost d B ≤ ∑ i ∈ B, α i) ∧
      ∃ C' ⊆ Cout, C'.card ≤ 2 * Ccore.card ∧ ∃ blocks : Finset (Finset D),
        (blocks : Set (Finset D)).PairwiseDisjoint id ∧
        (∀ B ∈ blocks, B.card = 2 * Ccore.card) ∧ blocks.biUnion id = Cout \ C' := by sorry

end MinSumClust
