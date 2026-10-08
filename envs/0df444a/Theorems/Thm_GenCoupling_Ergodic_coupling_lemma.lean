-- Prove2me | Theorems.Thm_GenCoupling_Ergodic_coupling_lemma
-- name    : GenCoupling.Ergodic.coupling_lemma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:43.414118+00:00
-- url     : https://prove2.me/theorems/cfa9b1c6-d676-4728-92b8-76243e4f242d
-- title:
--   Proof of Theorem 2.3(i), p. 8 — coupling lemma: some coupling of µ, ν has P(X ≠ Y) = d_TV(µ, ν)
-- statement:
--   Let $E$ be a Polish space with its Borel $\sigma$-field and let $\mu,\nu$ be Borel probability measures on $E$. Then there is a coupling $\gamma\in\mathcal C(\mu,\nu)$, that is a probability measure on $E\times E$ with marginals $\mu$ and $\nu$, such that
--   $$\gamma\{(x,y):x\neq y\}=d_{TV}(\mu,\nu)=\sup_{A\in\mathcal E}|\mu(A)-\nu(A)|.$$
--   Equivalently, there are random variables $\hat Y\sim\mu$, $Z\sim\nu$ with $\mathsf P(\hat Y\ne Z)=d_{TV}(\mu,\nu)$ (a maximal coupling).
--
--   The proof of Theorem 2.3(i) applies this to $\mu=\mathrm{Law}(Y^{x,y}_t)$ and $\nu=P_t(y,\cdot)$, citing [43, Theorem 4.1]; it is the "reimburse" half of the Control-and-Reimburse strategy.
--
--   **Formalization Note** Stated for arbitrary Borel probability measures, not only for the two measures the page names.
-- source:
--   Butkovsky, Kulik and Scheutzow, Generalized couplings and ergodic rates for SPDEs and other Markov models, arXiv:1806.00395v3, p. 8, proof of Theorem 2.3(i), "by Assumption A.1 and the coupling lemma (see, e.g., [43, Theorem 4.1])"

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_GenCoupling_Ergodic_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GenCoupling.Ergodic

/-- Coupling lemma (proof of Theorem 2.3(i), p. 8): for Borel probability measures `μ, ν` on a
Polish space there is a coupling `γ ∈ C(μ, ν)` with `γ{x ≠ y} = d_TV(μ, ν)`. -/
theorem coupling_lemma {E : Type*} [MetricSpace E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∃ γ ∈ couplings μ ν, (γ {p : E × E | p.1 ≠ p.2}).toReal = MarkovChainCLT.tvDist μ ν := by sorry

end GenCoupling.Ergodic
