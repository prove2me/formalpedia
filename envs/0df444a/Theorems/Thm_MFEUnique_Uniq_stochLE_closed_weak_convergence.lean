-- Prove2me | Theorems.Thm_MFEUnique_Uniq_stochLE_closed_weak_convergence
-- name    : MFEUnique.Uniq.stochLE_closed_weak_convergence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:56.31362+00:00
-- url     : https://prove2.me/theorems/0403a775-6d73-489b-82f0-caeac38e8feb
-- title:
--   p. 13 (Kamae et al. 1977) — ⪰SD is closed under weak convergence
-- statement:
--   Let $X$ be a compact metric space with a closed partial order and its Borel $\sigma$-algebra. Let $(\mu_n)$ and $(\nu_n)$ be sequences of probability measures on $X$ with $\mu_n \succeq_{SD} \nu_n$ for every $n$, and suppose $\mu_n \to \mu$ and $\nu_n \to \nu$ weakly for probability measures $\mu, \nu$. Then
--   $$\mu \succeq_{SD} \nu.$$
--
--   In the proof of Theorem 1 this transfers the comparison $M_{s_1}^n\theta_1 \succeq_{SD} M_{s_2}^n\theta_2$ to the weak limits $s_1$ and $s_2$.
--
--   **Formalization Note** The sequences are general measures with the added hypothesis that each is a probability measure (true for the iterates of a Markov operator; without it the integrals against bounded functions could be junk). Weak convergence is the p. 7 definition with bounded continuous test functions. $\succeq_{SD}$ is `StochLE` with swapped arguments; its test functions are bounded measurable increasing, not only continuous ones, which is why the closedness of the order is required.
-- source:
--   Light and Weintraub, Mean Field Equilibrium: Uniqueness, Existence, and Comparative Statics, arXiv:1903.02273v3, p. 13, proof of Theorem 1, second paragraph (citing Kamae, Krengel and O'Brien 1977)

import Mathlib
import Definitions.Def_MFEUnique_Uniq_Equilibrium

open MeasureTheory StochIneqPO.Comparison

namespace MFEUnique.Uniq

/-- p. 13, proof of Theorem 1 (citing Kamae et al. 1977): `⪰SD` is closed under weak
convergence. If `μ_n ⪰SD ν_n` for every `n`, `μ_n → μ` and `ν_n → ν` weakly, then `μ ⪰SD ν`. -/
theorem stochLE_closed_weak_convergence {X : Type*} [MetricSpace X] [CompactSpace X]
    [PartialOrder X] [OrderClosedTopology X] [MeasurableSpace X] [BorelSpace X]
    (μn νn : ℕ → Measure X) (hμn : ∀ n, IsProbabilityMeasure (μn n))
    (hνn : ∀ n, IsProbabilityMeasure (νn n)) (μ ν : ProbabilityMeasure X)
    (hμ : WeakConv μn (μ : Measure X)) (hν : WeakConv νn (ν : Measure X))
    (h : ∀ n, StochLE (νn n) (μn n)) :
    StochLE (ν : Measure X) (μ : Measure X) := by sorry

end MFEUnique.Uniq
