-- Prove2me | Theorems.Thm_IdentityTesting39_ExactRadius_sec4_upper_test
-- name    : IdentityTesting39.ExactRadius.sec4_upper_test
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:37.009188+00:00
-- url     : https://prove2.me/theorems/669875b6-171a-4f06-8ac9-9f10c20e1287
-- title:
--   §4 — the three-statistic test and fixed-sample upper bound
-- statement:
--   There are absolute positive constants $A,J_{\rm up},J_{\rm fixed},C$. Fix a probability reference $q$, nonempty strict radius $\varepsilon$, real $n>0$, and a separating optimizer of an applicable branch with value $J\ge J_{\rm up}$. Under independent $X_i\sim\operatorname{Poi}(np_i)$ use
--
--   $$L=\sum a_i(X_i-nq_i),\quad Q=\sum b_i((X_i-nq_i)^2-X_i),\quad V=\sum a_i^2X_i.$$
--
--   Reject if $L>J/2$, $Q>J/2$, or $V>AJ$. Both errors are at most $1/10$ against deterministic alternatives feasible in the branch. Under the null, $\operatorname{Var}L\le9J$, $\operatorname{Var}Q\le8J$, $\mathbb EV\le9J$, and the rejection probability is at most $68/J+9/A$.
--
--   For any probability vector $p$, set $E=n^2\sum b_i(p_i-q_i)^2$ and $v=\operatorname{Var}_pL$. The expectation of $Q$ is $E$, its variance is $2n^2\sum b_i^2p_i^2+4n^3\sum b_i^2p_i(p_i-q_i)^2$, and it is at most $16J+4E+8\sqrt J E+4E^{3/2}$. Also $nb_iq_i\le2\sqrt J$, $v=\mathbb E_pV$, and $\operatorname{Var}_pV\le9v$. The high-variance and controlled-linear-variance failure bounds are respectively $18/(AJ)$ and $8A/J$ in the source's regimes.
--
--   Off the point mass, if every relevant branch containing a strict alternative has value at least $J_{\rm fixed}$, some admissible $m\le C(n+1)$ exists and $N^*\le C(n+1)$. This includes omission of exactly the empty strict branches and the fixed-block Poisson conversion.
--
--   Differences from the source:
--   - encoding: a finite domain with k labels → an arbitrary finite label type ι, with k its cardinality; reason: finite relabeling changes no instance and permits the reservoir quotient
--   - reading: least fixed sample size permitting the two error bounds in §2 → tests are rejection-probability functions with values in [0,1]; reason: Appendix A explicitly uses randomized testers and §4 uses internal Poisson-simulation randomness
--   - encoding: minima over scalar tuples on the relevant coordinates → law-defined moments, real infima with explicit attainment where asserted, and zero unused head slots; reason: zeroing unused slots is a coordinate convention; infeasible deficit values are never used
--   - encoding: universal O or Ω comparison constants → positive existential constants precede all instance data and label types; reason: this is the universal meaning of the source asymptotics
--   - encoding: omit deficit when ε≥α and excess when ε≥1−min_tail q_i → a branch is used exactly when a strict deterministic alternative exists in it; reason: the same omission rule is expressed without taking a minimum over an empty tail
--   - encoding: E^{3/2} for nonnegative E → E times sqrt(E); reason: the quadratic signal is nonnegative, so these coincide
-- source:
--   Zhijie Zheng, An Exact-Radius Convex Characterization of Discrete Identity Testing, STOC 2027 submission #39 (October 2026), p.5, §4, statistics L,Q,V and fixed-block conversion, continuing on p.6; constants: Appendix C.5, p.21; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/39.pdf

import Definitions.Def_IdentityTesting39_ExactRadius_PoissonExperiments

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace IdentityTesting39.ExactRadius

/-- §4, printed pp.5–6 / PDF pp.6–7, including the fixed-block conversion. -/
theorem sec4_upper_test :
    ∃ A Jup Jfixed C : ℝ, 0 < A ∧ 0 < Jup ∧ 0 < Jfixed ∧ 0 < C ∧
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (q : ι → ℝ) (ε n : ℝ)
      (B : Branch ι) (x : MomentFamily ι) (θ : ℝ),
      ProbabilityVector q → StrictRadius q ε → 0 < n →
      InRegime q B → SeparatingOptimizer q ε n B x θ → Jup ≤ programValue q ε n B →
      let J := programValue q ε n B
      let a := aVector q x
      let b := bVector q B x
      let L := linearStatistic q a n
      let Q := quadraticStatistic q b n
      let V := varianceStatistic a
      let reject := rejectEvent q a b n J A
      variance L (poissonExperiment n q) ≤ 9*J ∧
      variance Q (poissonExperiment n q) ≤ 8*J ∧
      (∫ X, V X ∂poissonExperiment n q) ≤ 9*J ∧
      (poissonExperiment n q reject).toReal ≤ 68/J+9/A ∧
      (poissonExperiment n q reject).toReal ≤ 1/10 ∧
      (∀ p, ProbabilityVector p →
        let E := n^2*(∑ i, b i*(p i-q i)^2)
        let v := variance L (poissonExperiment n p)
        (∫ X, Q X ∂poissonExperiment n p) = E ∧
        variance Q (poissonExperiment n p) =
          2*n^2*(∑ i, (b i)^2*(p i)^2) + 4*n^3*(∑ i, (b i)^2*p i*(p i-q i)^2) ∧
        variance Q (poissonExperiment n p) ≤
          16*J+4*E+8*Real.sqrt J*E+4*E*Real.sqrt E ∧
        (∀ i, n*b i*q i ≤ 2*Real.sqrt J) ∧
        v = ∫ X, V X ∂poissonExperiment n p ∧
        variance V (poissonExperiment n p) ≤ 9*v ∧
        (2*A*J ≤ v →
          (poissonExperiment n p {X | V X ≤ A*J}).toReal ≤ 18/(A*J)) ∧
        (v < 2*A*J → J ≤ ∫ X, L X ∂poissonExperiment n p →
          (poissonExperiment n p {X | L X ≤ J/2}).toReal ≤ 8*A/J) ∧
        (deterministicTuple q p B ∈ feasibleMoments q ε B →
          (poissonExperiment n p rejectᶜ).toReal ≤ 1/10))) ∧
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (q : ι → ℝ) (ε n : ℝ) (i₀ : ι),
      ProbabilityVector q → StrictRadius q ε → Largest q i₀ → q i₀ < 1 → 0 < n →
      (∀ B : Branch ι, RelevantBranch q i₀ B → StrictBranch q ε B →
        Jfixed ≤ programValue q ε n B) →
      (∃ m ∈ admissibleSizes q ε, (m : ℝ) ≤ C*(n+1)) ∧
      (sampleComplexity q ε : ℝ) ≤ C*(n+1)) := by sorry

end IdentityTesting39.ExactRadius
