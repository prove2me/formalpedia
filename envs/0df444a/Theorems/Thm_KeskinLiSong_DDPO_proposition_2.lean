-- Prove2me | Theorems.Thm_KeskinLiSong_DDPO_proposition_2
-- name    : KeskinLiSong.DDPO.proposition_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:50:27.515929+00:00
-- url     : https://prove2.me/theorems/6aa3668d-87fa-4ce4-9b5f-7fa3f37b9ea2
-- title:
--   Proposition 2 — demand MQLE tail
-- statement:
--   Consider the model of Sections 2–3: real compact price and inventory intervals, an increasing C2 link, piecewise-constant demand parameters with C separated changes, independent centered locally light-tailed noise, and independent beta perishability. Costs satisfy the printed restriction. Estimators and policies are the concrete DDPO constructions, with measurable choices among genuine optimizers. The positive constants precede every horizon, allowed environment, period and change index. Both DDPO schedules are covered. The full interval tau*_j < tau(t) < tau_minus_j is retained, including the pre-first-detection portion. No clean-data premise is inserted.
--
--   $$
--   \mathbb P\!\left(\|\widehat\theta_t-\theta_t\|^2\ge K_3\frac{\log M_t}{M_t}\right)\le\frac{K_4}{M_t}.
--   $$
--
--   The full source statement, including all definitions and clauses, is:
--
--   PROPOSITION 2. For any period t∉𝒳 in cycle τ with τ*_j < τ < τ̂_j^−, there exist positive constants K_3
--   and K_4 such that
--   P^π_{θ,ξ}{‖θ̂_t−θ_t‖² ≥ K_3 log M_t/M_t} ≤ K_4/M_t. (23)
--
--   Differences from the source:
--   - reading: equation (6) uses alpha + beta p in the demand law → the law uses g(alpha + beta p); reason: equations (1) and (2) specify the general link; source finding I1
--   - encoding: expectations and probabilities under the observation law → coupled independent infinite primitive sequences with separate recursively generated policy histories; reason: the measurable history recursion induces the observation law and preserves every finite-horizon instance
--   - reading: tail bounds have random sample sizes and random qualifying cycle ranges → the scalar event probability is bounded almost surely by the random right side on the stated range; reason: literal random-inequality interpretation; neither conditioning nor averaging replaces the displayed bound
--   - generalization: the surrounding model supposes an interior FIA optimum exists → this statement does not require an FIA existence premise; reason: adding that source premise specializes the statement; its estimators, proxies, derivatives or unconstrained-regret contributions do not use the FIA benchmark
--   - reading: Section 5.2 presents the MQLE calculation for N and uses it for E in Theorem 2(b) → the same statement is quantified over either DDPO schedule; reason: the demand estimator is shared by both policies; no noise-parametric hypothesis is added to the N branch
--   - reading: the link g is increasing → g is nondecreasing and twice continuously differentiable; reason: increasing is read in its weak monotonicity sense; no strictly positive derivative or inverse-sensitivity assumption is printed
-- source:
--   Keskin, Li and Song (2022), Data-Driven Dynamic Pricing and Ordering with Perishable Inventory in a Changing Environment, Management Science, doi:10.1287/mnsc.2021.4011, supplied source.pdf (internally dated January 3, 2021; SSRN 3401188 footers), Proposition 2, printed p. 21 (PDF p. 21)

import Definitions.Def_KeskinLiSong_DDPO_Uniformity

open MeasureTheory ProbabilityTheory

namespace KeskinLiSong.DDPO

theorem proposition_2 (A : Model) (u : Tuning A) (mode : NoiseMode)
    (hmode : mode.Fits A.noise.law) :
    ∃ K3 K4 : ℝ, 0 < K3 ∧ 0 < K4 ∧
    ∀ (T : ℕ) (E : Environment A T) (L : Learner mode),
      Executes mode A u E L →
      ∀ t ∈ Finset.Icc 1 T, t ∉ experimental u mode.version T → ∀ j ≤ A.changes,
      TailBound (primitiveLaw A E)
        (fun z => changeCycle A u mode.version E j < cycleAt u mode.version T t ∧
          cycleAt u mode.version T t < detectionMinus A u mode.version E (demandPath A E L.policy z) j)
        (fun z => ‖thetaEstimate mode A E L z t - E.theta t‖ ^ 2)
        (fun z => K3 * Real.log (effectiveSize mode A u E L z t) /
          effectiveSize mode A u E L z t)
        (fun z => K4 / effectiveSize mode A u E L z t) := by sorry

end KeskinLiSong.DDPO
