-- Prove2me | Theorems.Thm_KeskinLiSong_DDPO_proposition_6
-- name    : KeskinLiSong.DDPO.proposition_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:50:41.496899+00:00
-- url     : https://prove2.me/theorems/6895bd32-aa9a-4b7f-a3be-b11701b67fec
-- title:
--   Proposition 6 — grid pricing convergence
-- statement:
--   Consider the model of Sections 2–3: real compact price and inventory intervals, an increasing C2 link, piecewise-constant demand parameters with C separated changes, independent centered locally light-tailed noise, and independent beta perishability. Costs satisfy the printed restriction. Estimators and policies are the concrete DDPO constructions, with measurable choices among genuine optimizers. The statement covers every nonexperimental DDPO-N period. The comparator is any genuine joint optimizer with the true demand and perishability parameters. The denominator of the probability bound is sqrt(M_t log M_t), with both factors inside the radical. No derivative lower bound or strong concavity is assumed.
--
--   $$
--   \mathbb P\!\left(|p_t^u-\widehat p_t|\ge K_{11}\sqrt{\frac{\log M_t}{M_t}}\right)\le\frac{K_{12}}{\sqrt{M_t\log M_t}}.
--   $$
--
--   The full source statement, including all definitions and clauses, is:
--
--   PROPOSITION 6. For the DDPO-N policy, there exist positive constants K_11 and K_12 such that, for any
--   period t∉𝒳,
--   P^π_{θ,ξ}{|p_t^u−p̂_t|≥K_11√(log M_t/M_t)}≤K_12/√(M_t log M_t). (29)
--
--   Differences from the source:
--   - reading: equation (6) uses alpha + beta p in the demand law → the law uses g(alpha + beta p); reason: equations (1) and (2) specify the general link; source finding I1
--   - encoding: expectations and probabilities under the observation law → coupled independent infinite primitive sequences with separate recursively generated policy histories; reason: the measurable history recursion induces the observation law and preserves every finite-horizon instance
--   - reading: tail bounds have random sample sizes and random qualifying cycle ranges → the scalar event probability is bounded almost surely by the random right side on the stated range; reason: literal random-inequality interpretation; neither conditioning nor averaging replaces the displayed bound
--   - generalization: the surrounding model supposes an interior FIA optimum exists → this statement does not require an FIA existence premise; reason: adding that source premise specializes the statement; its estimators, proxies, derivatives or unconstrained-regret contributions do not use the FIA benchmark
--   - reading: the link g is increasing → g is nondecreasing and twice continuously differentiable; reason: increasing is read in its weak monotonicity sense; no strictly positive derivative or inverse-sensitivity assumption is printed
-- source:
--   Keskin, Li and Song (2022), Data-Driven Dynamic Pricing and Ordering with Perishable Inventory in a Changing Environment, Management Science, doi:10.1287/mnsc.2021.4011, supplied source.pdf (internally dated January 3, 2021; SSRN 3401188 footers), Proposition 6, printed p. 23 (PDF p. 23)

import Definitions.Def_KeskinLiSong_DDPO_Uniformity

open MeasureTheory ProbabilityTheory

namespace KeskinLiSong.DDPO

theorem proposition_6 (A : Model) (u : Tuning A) :
    ∃ K11 K12 : ℝ, 0 < K11 ∧ 0 < K12 ∧
    ∀ (T : ℕ) (E : Environment A T) (L : Learner .nonparametric),
      Executes .nonparametric A u E L →
      ∀ t ∈ Finset.Icc 1 T, t ∉ experimental u .N T →
      ∀ opt : Action, JointOptimum A A.noise.law (E.theta t) E.xi opt →
      TailBound (primitiveLaw A E) (fun _ => True)
        (fun z => |opt.1 - (actionAt A E L.policy z t).1|)
        (fun z => K11 * Real.sqrt (Real.log (effectiveSize .nonparametric A u E L z t) /
          effectiveSize .nonparametric A u E L z t))
        (fun z => K12 / Real.sqrt (effectiveSize .nonparametric A u E L z t *
          Real.log (effectiveSize .nonparametric A u E L z t))) := by sorry

end KeskinLiSong.DDPO
