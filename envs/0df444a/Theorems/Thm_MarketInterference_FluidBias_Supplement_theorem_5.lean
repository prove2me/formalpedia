-- Prove2me | Theorems.Thm_MarketInterference_FluidBias_Supplement_theorem_5
-- name    : MarketInterference.FluidBias.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:47:38.052802+00:00
-- url     : https://prove2.me/theorems/fe6f0561-2783-4927-a1f6-7f58e233f439
-- title:
--   Theorem 5 (corrected: refuted even after variance reduction) — unique arc optima do not ensure variance limits
-- statement:
--   Theorem 5's displayed limits need not exist even for the variance-reduced RCT estimator specified by the remark on p.42. Consider two demand types, two supply types and one intermediate node. Both supplies feed that node; it feeds both demands. Values on the supply arcs are 2 and 1, and values on the demand arcs are 1 and 0. Every arc capacity is 3. Let demand rates be (1,3), supply rates (1,1), treatment effect zero and treatment fraction 1/2.
--
--   The fluid optimal arc flow is uniquely (1,1,1,1). The whole dual is uniquely a=(1,0), b=(2,1), m=0 and ξ=0. Two optimal path decompositions nevertheless pair the supplies with demands differently. At even densities pair supply 0 with demand 0 as much as possible; at odd densities pair supply 1 with demand 0 as much as possible. Complete the remaining optimal flow and allocate the observed control labels uniformly within each demand type. Both are integer blind allocations under the actual independent Poisson counts.
--
--   Let R_n be the conditional expectation of the realized RCT estimator given all control, treatment and supply counts, at density n. The constructed allocations satisfy
--   $$
--   \lim_{m\to\infty}\operatorname{Var}(\sqrt{2m}\,R_{2m})=\frac{112}{3},\qquad
--   \lim_{m\to\infty}\operatorname{Var}(\sqrt{2m+1}\,R_{2m+1})=\frac{64}{3}.
--   $$
--   Consequently no real asymptotic RCT variance exists, whereas the corresponding SP variance tends to 4. All compared variables have finite second moments. This refutes the complete universal limit assertion, including the variance-reduced reading; it does not assert a reversed inequality between existing limits. DISPROOF.md gives the source anchors, the optimal pairings and the exact conditional-variance calculation.
--
--   **Formalization Note** The Lean sequence index n denotes density n+1. Its even-density subsequence is indexed by 2n+1 and its odd-density subsequence by 2n. The network and law are explicit helpers in RandomAllocation. Source type i+1 is Lean index i. The existential allocation family obeys the actual optimality, group-count and conditional-mean predicates and has integer group path flows. The raw estimator and its conditional expectation remain distinct. No variance convergence is assumed.
--
--   Differences from the source:
--   - correction: Assumptions 1–2 ensure existence and comparison of the asymptotic variance limits, including the p.42 variance-reduced RCT reading → an admissible two-demand two-supply network has unique fluid primal and whole-dual optima but variance-reduced RCT variance has distinct even/odd limits 112/3 and 64/3, while SP variance tends to 4; reason: Assumption 2 fixes arc flows in (2), not their path decomposition; the two optimal pairings in DISPROOF.md have different per-demand revenues and both satisfy the literal blindness equation
--   - encoding: density-indexed real variances of the actual source estimators → positive integer densities n+1, actual product Poisson laws, integer blind path allocations, conditional expectation given all counts and supply, and square-integrability conclusions; reason: the counterexample uses every source assumption and refutes the full limit assertion without default-valued variance or conditional expectation
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 23, Theorem 5, (13); p. 42, variance-reduction remark; pp. 47–48, proof

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_Supplement_RandomAllocation

namespace MarketInterference.FluidBias.Supplement

open MeasureTheory Filter

/-- Theorem 5 is false even with the variance-reduced RCT reading on p.42:
unique arc-flow optima do not fix the path decomposition. Two blind routing rules
have different asymptotic variances; alternating them destroys the displayed limit. -/
theorem theorem_5 :
    (∃! x, IsOptimal routingNetwork 1 routingDemand (fun _ => 1) x) ∧
    (∃! q, IsOptimalDual routingNetwork 1 routingDemand (fun _ => 1) q) ∧
    (∀ n, IsProbabilityMeasure (routingLaw (n + 1)) ∧
      HasExperimentLaw (routingLaw (n + 1)) Prod.fst routingDemand (fun _ => 0)
        (fun _ => 1) (1/2) (n + 1 : ℕ)) ∧
    ∃ A : ∀ n : ℕ, BlindAllocation routingNetwork (routingLaw (n + 1)) Prod.fst (n + 1 : ℕ),
      (∀ n, ∀ᵐ ω ∂routingLaw (n + 1), ∀ p, ∃ c t : ℕ,
        (A n).control ω p = (c : ℝ) ∧ (A n).treatment ω p = (t : ℝ)) ∧
      (∀ n,
        MemLp (rctEst routingNetwork (routingLaw (n + 1)) Prod.fst (1/2)
          (n + 1 : ℕ) (A n)) 2 (routingLaw (n + 1)) ∧
        MemLp (fun ω => Real.sqrt (n + 1 : ℕ) *
          reducedRCT routingNetwork (routingLaw (n + 1)) Prod.fst (1/2)
            (n + 1 : ℕ) (A n) ω) 2 (routingLaw (n + 1)) ∧
        MemLp (fun ω => Real.sqrt (n + 1 : ℕ) *
          observedSP routingNetwork Prod.fst (1/2) (n + 1 : ℕ) ω)
          2 (routingLaw (n + 1))) ∧
      (let V := fun n => ProbabilityTheory.variance
          (fun ω => Real.sqrt (n + 1 : ℕ) *
            reducedRCT routingNetwork (routingLaw (n + 1)) Prod.fst (1/2)
              (n + 1 : ℕ) (A n) ω) (routingLaw (n + 1))
       Tendsto (fun n => V (2 * n + 1)) atTop (nhds (112 / 3 : ℝ)) ∧
       Tendsto (fun n => V (2 * n)) atTop (nhds (64 / 3 : ℝ)) ∧
       ¬ ∃ v : ℝ, Tendsto V atTop (nhds v)) ∧
      Tendsto (fun n => ProbabilityTheory.variance
        (fun ω => Real.sqrt (n + 1 : ℕ) *
          observedSP routingNetwork Prod.fst (1/2) (n + 1 : ℕ) ω)
        (routingLaw (n + 1))) atTop (nhds 4) := by sorry

end MarketInterference.FluidBias.Supplement
