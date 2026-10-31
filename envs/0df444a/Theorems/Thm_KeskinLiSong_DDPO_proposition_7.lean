-- Prove2me | Theorems.Thm_KeskinLiSong_DDPO_proposition_7
-- name    : KeskinLiSong.DDPO.proposition_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:50:53.314465+00:00
-- url     : https://prove2.me/theorems/51f7f571-c050-4576-aec3-db52043e9dac
-- title:
--   Proposition 7 — inventory convergence
-- statement:
--   Consider the model of Sections 2–3: real compact price and inventory intervals, an increasing C2 link, piecewise-constant demand parameters with C separated changes, independent centered locally light-tailed noise, and independent beta perishability. Costs satisfy the printed restriction. Estimators and policies are the concrete DDPO constructions, with measurable choices among genuine optimizers. The comparator y_t^u(p_hat_t) is a genuine minimizer of H with theta_hat_t and xi_hat_t, exactly as the printed final line specifies. Any measurable choice among such optimizers is covered. The learner comparison is its unconstrained inventory decision. No density positivity, strict convexity or inverse-cdf Lipschitz condition is imposed.
--
--   $$
--   \mathbb P\!\left(|y_t^u(\widehat p_t)-\widehat y_t^u|\ge K_{13}\sqrt{\frac{\log M_t}{M_t}}\right)\le\frac{K_{14}}{M_t}.
--   $$
--
--   The full source statement, including all definitions and clauses, is:
--
--   PROPOSITION 7. For the DDPO-N policy, there exist positive constants K_13 and K_14 such that, for any
--   period t∉𝒳,
--   P^π_{θ,ξ}{|y_t^u(p̂_t)−ŷ_t^u|≥K_13√(log M_t/M_t)}≤K_14/M_t, (30)
--   where y_t^u(p̂_t) is the unconstrained optimum of H(y_t;p̂_t,θ̂_t,ξ̂_t).
--
--   Differences from the source:
--   - reading: equation (6) uses alpha + beta p in the demand law → the law uses g(alpha + beta p); reason: equations (1) and (2) specify the general link; source finding I1
--   - encoding: expectations and probabilities under the observation law → coupled independent infinite primitive sequences with separate recursively generated policy histories; reason: the measurable history recursion induces the observation law and preserves every finite-horizon instance
--   - reading: tail bounds have random sample sizes and random qualifying cycle ranges → the scalar event probability is bounded almost surely by the random right side on the stated range; reason: literal random-inequality interpretation; neither conditioning nor averaging replaces the displayed bound
--   - generalization: the surrounding model supposes an interior FIA optimum exists → this statement does not require an FIA existence premise; reason: adding that source premise specializes the statement; its estimators, proxies, derivatives or unconstrained-regret contributions do not use the FIA benchmark
--   - reading: the link g is increasing → g is nondecreasing and twice continuously differentiable; reason: increasing is read in its weak monotonicity sense; no strictly positive derivative or inverse-sensitivity assumption is printed
-- source:
--   Keskin, Li and Song (2022), Data-Driven Dynamic Pricing and Ordering with Perishable Inventory in a Changing Environment, Management Science, doi:10.1287/mnsc.2021.4011, supplied source.pdf (internally dated January 3, 2021; SSRN 3401188 footers), Proposition 7, printed p. 24 (PDF p. 24)

import Definitions.Def_KeskinLiSong_DDPO_Uniformity

open MeasureTheory ProbabilityTheory

namespace KeskinLiSong.DDPO

theorem proposition_7 (A : Model) (u : Tuning A) :
    ∃ K13 K14 : ℝ, 0 < K13 ∧ 0 < K14 ∧
    ∀ (T : ℕ) (E : Environment A T) (L : Learner .nonparametric),
      Executes .nonparametric A u E L →
      ∀ t ∈ Finset.Icc 1 T, t ∉ experimental u .N T →
      ∀ y : Paths T → ℝ, Measurable y →
        (∀ᵐ z ∂primitiveLaw A E,
          StockOptimum A A.noise.law (thetaEstimate .nonparametric A E L z t)
            (xiEstimate .nonparametric A E L z t) (actionAt A E L.policy z t).1 (y z)) →
      TailBound (primitiveLaw A E) (fun _ => True)
        (fun z => |y z - (evaluate A E L.policy L.optimum z t).2|)
        (fun z => K13 * Real.sqrt (Real.log (effectiveSize .nonparametric A u E L z t) /
          effectiveSize .nonparametric A u E L z t))
        (fun z => K14 / effectiveSize .nonparametric A u E L z t) := by sorry

end KeskinLiSong.DDPO
