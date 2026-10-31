-- Prove2me | Theorems.Thm_KeskinLiSong_DDPO_proposition_4
-- name    : KeskinLiSong.DDPO.proposition_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:51:48.772774+00:00
-- url     : https://prove2.me/theorems/76e9e885-3405-4581-89d6-9ebd33209322
-- title:
--   Proposition 4 — true-noise empirical proxy
-- statement:
--   Consider the model of Sections 2–3: real compact price and inventory intervals, an increasing C2 link, piecewise-constant demand parameters with C separated changes, independent centered locally light-tailed noise, and independent beta perishability. Costs satisfy the printed restriction. Estimators and policies are the concrete DDPO constructions, with measurable choices among genuine optimizers. The probability integrates only the noise sequence, for almost every fixed perishability sequence. Prices are allowed to depend on observed history. All reset times, estimated beta parameters and sample sizes are recomputed under that integration. The absolute difference uses the true-theta, true-noise empirical proxy and the same estimated beta parameter.
--
--   $$
--   \mathbb P_\varepsilon\!\left(|G^u(p_t)-\widetilde G_t(p_t)|\ge K_7\sqrt{\frac{\log M_t}{M_t}}\right)\le\frac{K_8}{M_t}.
--   $$
--
--   The full source statement, including all definitions and clauses, is:
--
--   PROPOSITION 4. Given p_t∈P in period t∉𝒳, there exist positive constants K_7 and K_8 such that
--   P_ε{|G^u(p_t;θ_t,ξ̂_t)−G̃_t(p_t;θ_t,ξ̂_t,ε)|≥K_7√(log M_t/M_t)}≤K_8/M_t. (27)
--
--   Differences from the source:
--   - reading: equation (6) uses alpha + beta p in the demand law → the law uses g(alpha + beta p); reason: equations (1) and (2) specify the general link; source finding I1
--   - encoding: expectations and probabilities under the observation law → coupled independent infinite primitive sequences with separate recursively generated policy histories; reason: the measurable history recursion induces the observation law and preserves every finite-horizon instance
--   - reading: tail bounds have random sample sizes and random qualifying cycle ranges → the scalar event probability is bounded almost surely by the random right side on the stated range; reason: literal random-inequality interpretation; neither conditioning nor averaging replaces the displayed bound
--   - generalization: the surrounding model supposes an interior FIA optimum exists → this statement does not require an FIA existence premise; reason: adding that source premise specializes the statement; its estimators, proxies, derivatives or unconstrained-regret contributions do not use the FIA benchmark
--   - reading: the link g is increasing → g is nondecreasing and twice continuously differentiable; reason: increasing is read in its weak monotonicity sense; no strictly positive derivative or inverse-sensitivity assumption is printed
--   - reading: P_epsilon and E_epsilon govern the noise sequence while the beta estimate is random → integrate the noise sequence for almost every fixed perishability sequence, recomputing histories and estimates; reason: equation (6) supplies independent primitive sequences; the noise-only subscript does not replace estimated parameters by independent constants
--   - reading: a given price p_t in P → any measurable price selection from the preceding observed history; reason: period prices in Sections 2 and 3 use that information; constants are uniform over those selections within the compact price interval
-- source:
--   Keskin, Li and Song (2022), Data-Driven Dynamic Pricing and Ordering with Perishable Inventory in a Changing Environment, Management Science, doi:10.1287/mnsc.2021.4011, supplied source.pdf (internally dated January 3, 2021; SSRN 3401188 footers), Proposition 4, printed p. 22 (PDF p. 22)

import Definitions.Def_KeskinLiSong_DDPO_Uniformity

open MeasureTheory ProbabilityTheory

namespace KeskinLiSong.DDPO

theorem proposition_4 (A : Model) (u : Tuning A) :
    ∃ K7 K8 : ℝ, 0 < K7 ∧ 0 < K8 ∧
    ∀ (T : ℕ) (E : Environment A T) (L : Learner .nonparametric),
      Executes .nonparametric A u E L →
      ∀ t ∈ Finset.Icc 1 T, t ∉ experimental u .N T →
      ∀ p : PriceSelection,
        (∀ᵐ z ∂primitiveLaw A E, priceAt A E L.policy p z t ∈ A.P) →
      ∀ᵐ q ∂perishSequenceLaw A E,
      TailBound (noiseSequenceLaw A.noise) (fun _ => True)
        (fun e => let z := combine e q
          |G A A.noise.law (E.theta t) (xiEstimate .nonparametric A E L z t)
            (priceAt A E L.policy p z t) -
            trueProxy .nonparametric A u E L z t (priceAt A E L.policy p z t)|)
        (fun e => let z := combine e q
          K7 * Real.sqrt (Real.log (effectiveSize .nonparametric A u E L z t) /
            effectiveSize .nonparametric A u E L z t))
        (fun e => K8 / effectiveSize .nonparametric A u E L (combine e q) t) := by sorry

end KeskinLiSong.DDPO
