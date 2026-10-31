-- Prove2me | Theorems.Thm_GMFGLearn_appendixA_metric_complete
-- name    : GMFGLearn.appendixA_metric_complete
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:54:27.711032+00:00
-- url     : https://prove2.me/theorems/75cb9ad9-bf79-40ac-a1e7-6497553106ed
-- title:
--   Appendix A — $D$ and $W_1$ are finite distances, and $(\Pi,D)$ and $(\mathcal P(\mathcal S\times\mathcal A),W_1)$ are complete
-- statement:
--   Let $\mathcal S$ and $\mathcal A$ be nonempty compact metric spaces, $W_1$ the Wasserstein distance on $\mathcal P(\mathcal S\times\mathcal A)$ with the $\ell_2$ product cost, and $D(\pi,\pi')=\sup_sW_1(\pi(s),\pi'(s))$ on the measurable policies $\Pi$. Then:
--
--   1. $W_1$ is a distance on $\mathcal P(\mathcal S\times\mathcal A)$ ($W_1(\mathcal L,\mathcal L)=0$, symmetry, triangle inequality, $W_1(\mathcal L,\mathcal L')=0\Rightarrow\mathcal L=\mathcal L'$), it is finite, $0\le W_1\le\operatorname{diam}(\mathcal S\times\mathcal A)$, and every $W_1$-Cauchy sequence $W_1$-converges;
--   2. $D$ is a distance on $\Pi$, finite, $0\le D\le\operatorname{diam}(\mathcal A)$, and every $D$-Cauchy sequence of policies $D$-converges to a policy.
--
--   Completeness of $(\mathcal P(\mathcal S\times\mathcal A),W_1)$ is what lets the Banach fixed-point theorem produce the equilibrium of Theorem 1.
--
--   Differences from the source:
--   - generalization: compact S ⊆ ℝ^d, A ⊆ ℝ^p with Euclidean distances → nonempty compact metric spaces with Borel σ-fields, S×A with the cost √(d_S² + d_A²); reason: §2.1 states compact metric spaces; for Euclidean subsets the cost is the Euclidean distance of S×A ⊆ ℝ^{d+p}, so the source's case is an instance
--   - reading: "finite for any input distribution pairs" → the bounds 0 ≤ W₁ ≤ diam(S×A) and 0 ≤ D ≤ diam(A); reason: these are the bounds the proof of Lemma 8 gives for finiteness
--   - reading: Π := {π | π : S → P(A)} → the measurable maps S → P(A); reason: §2.2, p.4, and Notations, p.3: policies are measurable; the limit of a D-Cauchy sequence is again measurable
--   - encoding: "complete metric spaces" → the metric axioms plus convergence of every Cauchy sequence in the distance; reason: the definition of a complete metric space, written out
-- source:
--   Guo, Hu, Xu, Zhang, A General Framework for Learning Mean-Field Games, arXiv:2003.06069v3, Appendix A, after Lemma 8, p.36

import Mathlib
import Definitions.Def_GMFGLearn_GMFG

open MeasureTheory

namespace GMFGLearn

/-- **`D` and `W₁` are finite distance functions, and `(Π, D)` and `(P(S × A), W₁)` are complete.**
Guo–Hu–Xu–Zhang, *A General Framework for Learning Mean-Field Games*, arXiv:2003.06069v3,
Appendix A, after Lemma 8, p.36: "The same argument for Lemma 8 shows that both D and W1 are
distance functions and are finite for any input distribution pairs, with both (Π,D) and
(P(S×A),W1) again complete metric spaces."

**Formalization Note** `S`, `A` are nonempty compact metric spaces with their Borel σ-algebras
(§2.1, p.3); `W₁` on `P(S × A)` uses the ℓ₂ product cost `dSA`, and `D` is (14). "Distance
function" is stated as the metric axioms; "finite" as the bounds `0 ≤ W₁ ≤ diam(S × A)` and
`0 ≤ D ≤ diam(A)` the proof of Lemma 8 gives; completeness as: every Cauchy sequence converges in
the distance. -/
theorem appendixA_metric_complete {S A : Type*}
    [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S] [Nonempty S]
    [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A] [Nonempty A] :
    ((∀ L : ProbabilityMeasure (S × A), W1 dSA L L = 0) ∧
      (∀ L L' : ProbabilityMeasure (S × A), W1 dSA L L' = W1 dSA L' L) ∧
      (∀ L L' L'' : ProbabilityMeasure (S × A), W1 dSA L L'' ≤ W1 dSA L L' + W1 dSA L' L'') ∧
      (∀ L L' : ProbabilityMeasure (S × A), W1 dSA L L' = 0 → L = L') ∧
      (∀ L L' : ProbabilityMeasure (S × A), 0 ≤ W1 dSA L L' ∧ W1 dSA L L' ≤ diamSA S A) ∧
      (∀ u : ℕ → ProbabilityMeasure (S × A),
        (∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, W1 dSA (u m) (u n) < ε) →
          ∃ L : ProbabilityMeasure (S × A),
            Filter.Tendsto (fun n => W1 dSA (u n) L) Filter.atTop (nhds 0))) ∧
    ((∀ π : Policy S A, D π π = 0) ∧
      (∀ π π' : Policy S A, D π π' = D π' π) ∧
      (∀ π π' π'' : Policy S A, D π π'' ≤ D π π' + D π' π'') ∧
      (∀ π π' : Policy S A, D π π' = 0 → π = π') ∧
      (∀ π π' : Policy S A, 0 ≤ D π π' ∧ D π π' ≤ Metric.diam (Set.univ : Set A)) ∧
      (∀ u : ℕ → Policy S A,
        (∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, D (u m) (u n) < ε) →
          ∃ π : Policy S A, Filter.Tendsto (fun n => D (u n) π) Filter.atTop (nhds 0))) := by sorry

end GMFGLearn
