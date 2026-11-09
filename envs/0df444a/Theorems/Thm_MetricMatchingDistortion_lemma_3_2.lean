-- Prove2me | Theorems.Thm_MetricMatchingDistortion_lemma_3_2
-- name    : MetricMatchingDistortion.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:21:06.753764+00:00
-- url     : https://prove2.me/theorems/8105f367-b8aa-4b13-8cac-6859fe343c40
-- title:
--   Lemma 3.2 — the random partition is balanced with $\mathbb E[W]\le 2n^\theta\,\mathrm{OPT}$
-- statement:
--   Let $\theta=\log_2(3/2)$. For every $n\ge1$, every ranking profile and every selection rule that proposes an admissible merge whenever two claimed prefixes overlap, every partition $\mathcal P$ returned by RandRepPartition (Algorithm 2) with positive probability is balanced, and for every pseudometric $d$ consistent with the rankings and every perfect matching $\pi^*$,
--   $$\mathbb E[W(\mathcal P,d)]\le 2n^\theta\,\mathrm{cost}(\pi^*,d).$$
--   In particular $\mathbb E[W(\mathcal P,d)]\le 2n^\theta\,\mathrm{OPT}$.
--
--   This is the partition used to complete the PS prefix in Equation (5).
--
--   Differences from the source:
--   - reading: Choose such clusters S, T by a fixed rule → a rule is a function of the current clusters and representatives (and of σ); reason: the state of Algorithm 2 is its clusters and representatives
--   - generalization: one fixed rule → every selection rule that proposes an admissible merge (overlapping, p = |S| ≥ q = |T|) whenever two claimed prefixes overlap; reason: any fixed rule is such a rule, so the statement specializes to the page's
--   - encoding: OPT = cost(M*, d) for an optimal matching M* → cost(π*, d) for every perfect matching π*; reason: OPT is the minimum over perfect matchings and the coefficient is nonnegative, so the two bounds are equivalent
--   - encoding: balanced partition P = (A_j, B_j)_{j=1}^m → labelling c : Fin n ⊕ Fin n → Fin n with as many agents as items per label; reason: the same partitions; unused labels have no agent, no item and w_j = 0
--   - encoding: Algorithm 2 returns P; E[W(P,d)] → every labelling in the support of the output law is balanced; E as the finite sum over labellings; reason: the law of a finite random object
--   - encoding: n ≥ 1 (standing, §2 p.9) → [NeZero n]; reason: the same condition as a type class
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), Lemma 3.2, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_MetricMatchingDistortion_IsConsistentPseudometric
import Definitions.Def_MetricMatchingDistortion_matchingCost
import Definitions.Def_MetricMatchingDistortion_IsBalanced
import Definitions.Def_MetricMatchingDistortion_randRepPartition

namespace MetricMatchingDistortion

/-- **Lemma 3.2 (Partition Bound).** Charikar et al., *Sublinear Metric Distortion for Matching*, arXiv:2611.05777 (held version,
sha256 fdf3452b…), Lemma 3.2, p.15 (PDF p.17): "Algorithm 2 returns a balanced partition P such that, for all d ∈ ρ(σ),
E[W(P, d)] ≤ 2n^θ OPT", with θ = log₂(3/2) (p.15) and OPT = cost(M∗, d) for an optimal matching
M∗ (§3, p.12).

For every ranking profile and every selection rule that proposes an admissible merge whenever two
claimed prefixes overlap: every labelling RandRepPartition returns with positive probability is
balanced, and for every consistent pseudometric `d` and every perfect matching `π*`,
`E[W(P, d)] ≤ 2 n^θ cost(π*, d)`.

**Formalization Note.** The page fixes one rule; the lemma is stated for every admissible rule
acting on the current clusters. The bound is stated against every perfect matching `π*`, which
for an optimal one is the page's `OPT`. -/
theorem lemma_3_2 (n : ℕ) [NeZero n] (rk : Ranking n) (rule : SelectionRule n)
    (hrule : IsSelectionRule rk rule) :
    (∀ c ∈ (randRepPartition rk rule).support, IsBalanced c) ∧
      ∀ d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ, IsConsistentPseudometric rk d →
        ∀ πstar : Equiv.Perm (Fin n),
          ∑ c, (randRepPartition rk rule c).toReal * partitionCost c d ≤
            2 * (n : ℝ) ^ theta * matchingCost πstar d := by sorry

end MetricMatchingDistortion
