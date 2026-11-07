-- Prove2me | Theorems.Thm_ImpatientMatching_lemma_B_1
-- name    : ImpatientMatching.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:51:08.682203+00:00
-- url     : https://prove2.me/theorems/097b1102-4182-420e-8707-cf41b0aceadc
-- title:
--   Lemma B.1 — stationarity under unit abandonment
-- statement:
--   Consider a finite-type matching system with independent Poisson arrivals and a stationary Markov policy, in which every agent who can wait has independent rate-one exponential patience and all other agents have zero patience. Let $Q(t)$ be the post-decision queue-length chain, $N(q)$ the total population of a state, and $\lambda_w$ the total arrival rate of the types that can wait.
--
--   On the states reachable from empty, the chain is irreducible and positive recurrent, with a unique invariant law $\nu$. Its law from empty converges to $\nu$ in total variation, and
--   $$\sup_{t\ge0}\mathbb E[N(Q(t))^2]\le\lambda_w+\lambda_w^2,\qquad\mathbb E_\nu N^2\le\lambda_w+\lambda_w^2.$$
--   Starting empty, the expectation of each queue length converges to its stationary mean.
--
--   This supplies the stationary law and moments used in the YES-instance bounds.
--
--   Differences from the source:
--   - encoding: fresh randomization → one Exp(1) coin per event, in a private coordinate of the seed space; reason: any randomization over the countable decision set is a measurable function of it
--   - encoding: positive recurrent on the reachable class → every reachable state has holding rate zero or satisfies the published PositiveRecurrentCT; reason: a state of holding rate zero is absorbing, namely the empty state of a system with no type that can wait; the published return-time expression reads 1/0 there
--   - generalization: the chain of a stationary Markov policy → every feasible rule (including rules that would match incompatible types) for the chain clauses, and every policy following it for the path clauses; reason: the source's policy is such a rule and such a policy, so the Lean specializes to the source
--   - encoding: moments and means in ℝ → lower integrals and sums in ℝ≥0∞; reason: nonnegative quantities; a bound cannot hold through a default value
--   - encoding: independent Poisson streams, one per type; nonanticipating decisions on the observed history and internal randomization → one marked Poisson stream of rate Λ, the published admissible filtration, which also shows the virtual departure times of agents already matched; reason: same law for the arrivals; those extra times are independent of the future, so they act as private randomization
-- source:
--   C. Yan and S. M. Varma, Impatience Makes Matching NP-Hard, manuscript (sha256 7b1051b6c661435675185b0663cb08ab217698a2c4ee07fa0f473686dbb6bed9), Lemma B.1, (34), p.27

import Definitions.Def_ImpatientMatching_MarkovRule

open MeasureTheory
open scoped ENNReal
open DynStochMatching.Reward MatrixAnalytic.ProductForm

namespace ImpatientMatching

/-- **Lemma B.1 (stationarity under unit abandonment).** Yan–Varma, manuscript (sha256 7b1051b6…), (34), p.27: for a finite-type system with
a stationary Markov policy, in which each agent who can wait has rate-one patience and all others have
zero patience, the post-decision chain is irreducible and positive recurrent on the states reachable
from empty, with a unique invariant law `ν`. Its law from empty converges to `ν` in total variation,
`sup_t E[N(Q(t))²] ≤ λ_w + λ_w²`, `E_ν N² ≤ λ_w + λ_w²`, and each queue mean converges to its
stationary mean. The chain clauses hold for every feasible rule, and the path clauses for every
policy that follows it.

**Formalization Note.** A reachable state of holding rate zero is absorbing (it is the empty state of a
system with no type that can wait), and the published return-time expression reads `1/0` there,
so positive recurrence is stated for the states of positive holding rate. -/
theorem lemma_B_1 {n : ℕ} (D : Instance n) (hD : IsUnitPatience D) (rule : MarkovRule n)
    (hrule : IsFeasibleRule rule) :
    (∀ x ∈ reachable D rule, ∀ y ∈ reachable D rule, Reaches D rule x y) ∧
    (∀ x ∈ reachable D rule,
      holdRate (ruleGen D rule) x = 0 ∨ PositiveRecurrentCT (ruleGen D rule) x) ∧
    (∃! ν : State n → ℝ, IsInvariantLaw D rule ν) ∧
    (∀ ν : State n → ℝ, IsInvariantLaw D rule ν →
      nuMean ν (fun q => ((population q : ℝ≥0∞)) ^ 2) ≤
        ENNReal.ofReal (waitRate D + waitRate D ^ 2) ∧
      ∀ π : MatchingPolicy, Realizes D rule π →
        Filter.Tendsto (tvToLaw D π ν) Filter.atTop (nhds 0) ∧
        (∀ t : ℝ, 0 ≤ t →
          ∫⁻ ω, ((population (queueLen D π ω t) : ℝ≥0∞)) ^ 2 ∂seedLaw ≤
            ENNReal.ofReal (waitRate D + waitRate D ^ 2)) ∧
        ∀ i : Fin n, Filter.Tendsto
          (fun t : ℝ => ∫⁻ ω, (queueLen D π ω t i : ℝ≥0∞) ∂seedLaw) Filter.atTop
          (nhds (nuMean ν (fun q => (q i : ℝ≥0∞))))) := by sorry

end ImpatientMatching
