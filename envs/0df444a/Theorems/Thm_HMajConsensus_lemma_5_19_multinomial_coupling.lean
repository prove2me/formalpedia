-- Prove2me | Theorems.Thm_HMajConsensus_lemma_5_19_multinomial_coupling
-- name    : HMajConsensus.lemma_5_19_multinomial_coupling
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:13:42.083086+00:00
-- url     : https://prove2.me/theorems/213dd77c-9baa-4c88-9f15-b0cdf231dac1
-- title:
--   Lemma 5.19 — majorization-preserving coupling of $\mathrm{Multinomial}(n;a)$ and $\mathrm{Multinomial}(n;b)$
-- statement:
--   Let $a,b\in[0,1]^k$ be probability vectors with $a\succeq b$ (majorization, Definition 5.13), and let $n\ge1$. Then there is a jointly distributed pair $(U,V)$ of count vectors whose marginal distributions are
--   $$U\sim\mathrm{Multinomial}(n;a),\qquad V\sim\mathrm{Multinomial}(n;b),$$
--   such that $\Pr[U\succeq V]=1$.
--
--   The paper cites this coupling from Berenbrink et al. [BCEKMN17, §2.2 and Appendix A.3]; it turns the comparison of expected next-round distributions (Corollary 5.18) into a coupling of the actual next-round counts, which is the step of the proof of Theorem 5.14.
--
--   **Formalization Note** The joint law is a probability measure on pairs of count vectors in $\mathbb N^k\times\mathbb N^k$ whose two marginals are the multinomial laws (the count vector of $n$ iid samples). Majorization of count vectors is that of their real casts; $\Pr[U\succeq V]=1$ is stated almost surely.
--
--   Differences from the source:
--   - encoding: probability vectors a, b ∈ [0,1]^k; a pair (U, V); Pr[U ⪰ V] = 1 → a b : PMF (Fin k); a probability measure on (Fin k → ℕ) × (Fin k → ℕ) with the two multinomial marginals; Majorizes of the real casts holds almost surely; reason: a coupling is a joint law with the given marginals; same instances
-- source:
--   d'Amore, Rybicki, Shimizu, Shiraga, Vacus, Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics, arXiv:2610.40562, Lemma 5.19 (Multinomial coupling [BCEKMN17, Section 2.2 and Appendix A.3]), p.27

import Mathlib
import Definitions.Def_HMajConsensus_majLaw
import Definitions.Def_AgriSubsidy_Combined_Majorization

open MeasureTheory ProbabilityTheory

namespace HMajConsensus

/-- **Lemma 5.19** (d'Amore, Rybicki, Shimizu, Shiraga, Vacus, *Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics*, arXiv:2610.40562, §5.2, p.27; cited from [BCEKMN17, §2.2 and Appendix A.3]): let `a, b`
be probability vectors with `a ⪰ b`, and `n ≥ 1`. There is a jointly distributed pair `(U, V)`
with marginals `Multinomial(n; a)` and `Multinomial(n; b)` such that `Pr[U ⪰ V] = 1`.

**Formalization Note** The joint law is a probability measure on pairs of count vectors
`(Fin k → ℕ) × (Fin k → ℕ)`; majorization of count vectors is that of their real casts.
`Pr[U ⪰ V] = 1` is stated as "almost surely". -/
theorem lemma_5_19_multinomial_coupling {k : ℕ} (a b : PMF (Fin k))
    (hab : AgriSubsidy.Combined.Majorizes (probVec a) (probVec b)) (n : ℕ) (hn : 1 ≤ n) :
    ∃ μ : Measure ((Fin k → ℕ) × (Fin k → ℕ)), IsProbabilityMeasure μ ∧
      μ.map Prod.fst = multinomial n a ∧ μ.map Prod.snd = multinomial n b ∧
      ∀ᵐ x ∂μ, AgriSubsidy.Combined.Majorizes (fun i => (x.1 i : ℝ)) (fun i => (x.2 i : ℝ)) := by sorry

end HMajConsensus
