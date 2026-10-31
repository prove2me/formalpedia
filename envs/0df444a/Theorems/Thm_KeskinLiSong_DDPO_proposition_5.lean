-- Prove2me | Theorems.Thm_KeskinLiSong_DDPO_proposition_5
-- name    : KeskinLiSong.DDPO.proposition_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:51:37.85853+00:00
-- url     : https://prove2.me/theorems/fbeb98af-eda2-486c-a479-c628b49a4bc7
-- title:
--   Proposition 5 — residual profit proxy
-- statement:
--   Consider the model of Sections 2–3: real compact price and inventory intervals, an increasing C2 link, piecewise-constant demand parameters with C separated changes, independent centered locally light-tailed noise, and independent beta perishability. Costs satisfy the printed restriction. Estimators and policies are the concrete DDPO constructions, with measurable choices among genuine optimizers. The interval is exactly [tau_plus_j,tau_minus_j), with a closed left endpoint and an open right endpoint. The true-noise proxy uses theta_t; the residual proxy uses theta_hat_t. Both use the same estimated beta parameter and sample set. Constants precede horizons and all history-based price choices.
--
--   $$
--   \mathbb P\!\left(|\widetilde G_t(p_t)-\widehat G_t(p_t)|\ge K_9\sqrt{\frac{\log M_t}{M_t}}\right)\le\frac{K_{10}}{M_t}.
--   $$
--
--   The full source statement, including all definitions and clauses, is:
--
--   PROPOSITION 5. For any given p_t∈P in period t∉𝒳 of cycle τ∈[τ̂_j^+,τ̂_j^−), there exist positive
--   constants K_9 and K_10 such that
--   P^π_{θ,ξ}{|G̃_t(p_t;θ_t,ξ̂_t,ε)−Ĝ_t(p_t;θ̂_t,ξ̂_t,e)|≥K_9√(log M_t/M_t)}≤K_10/M_t. (28)
--
--   Differences from the source:
--   - reading: equation (6) uses alpha + beta p in the demand law → the law uses g(alpha + beta p); reason: equations (1) and (2) specify the general link; source finding I1
--   - encoding: expectations and probabilities under the observation law → coupled independent infinite primitive sequences with separate recursively generated policy histories; reason: the measurable history recursion induces the observation law and preserves every finite-horizon instance
--   - reading: tail bounds have random sample sizes and random qualifying cycle ranges → the scalar event probability is bounded almost surely by the random right side on the stated range; reason: literal random-inequality interpretation; neither conditioning nor averaging replaces the displayed bound
--   - generalization: the surrounding model supposes an interior FIA optimum exists → this statement does not require an FIA existence premise; reason: adding that source premise specializes the statement; its estimators, proxies, derivatives or unconstrained-regret contributions do not use the FIA benchmark
--   - reading: the link g is increasing → g is nondecreasing and twice continuously differentiable; reason: increasing is read in its weak monotonicity sense; no strictly positive derivative or inverse-sensitivity assumption is printed
--   - reading: a given price p_t in P → any measurable price selection from the preceding observed history; reason: period prices in Sections 2 and 3 use that information; constants are uniform over those selections within the compact price interval
-- source:
--   Keskin, Li and Song (2022), Data-Driven Dynamic Pricing and Ordering with Perishable Inventory in a Changing Environment, Management Science, doi:10.1287/mnsc.2021.4011, supplied source.pdf (internally dated January 3, 2021; SSRN 3401188 footers), Proposition 5, printed p. 23 (PDF p. 23)

import Definitions.Def_KeskinLiSong_DDPO_Uniformity

open MeasureTheory ProbabilityTheory

namespace KeskinLiSong.DDPO

theorem proposition_5 (A : Model) (u : Tuning A) :
    ∃ K9 K10 : ℝ, 0 < K9 ∧ 0 < K10 ∧
    ∀ (T : ℕ) (E : Environment A T) (L : Learner .nonparametric),
      Executes .nonparametric A u E L →
      ∀ t ∈ Finset.Icc 1 T, t ∉ experimental u .N T →
      ∀ p : PriceSelection,
        (∀ᵐ z ∂primitiveLaw A E, priceAt A E L.policy p z t ∈ A.P) →
      ∀ j ≤ A.changes,
      TailBound (primitiveLaw A E)
        (fun z => detectionPlus A u .N E (demandPath A E L.policy z) j ≤ cycleAt u .N T t ∧
          cycleAt u .N T t < detectionMinus A u .N E (demandPath A E L.policy z) j)
        (fun z => |trueProxy .nonparametric A u E L z t (priceAt A E L.policy p z t) -
          residualProxy .nonparametric A u E L z t (priceAt A E L.policy p z t)|)
        (fun z => K9 * Real.sqrt (Real.log (effectiveSize .nonparametric A u E L z t) /
          effectiveSize .nonparametric A u E L z t))
        (fun z => K10 / effectiveSize .nonparametric A u E L z t) := by sorry

end KeskinLiSong.DDPO
