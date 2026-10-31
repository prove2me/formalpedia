-- Prove2me | Theorems.Thm_KeskinLiSong_DDPO_theorem_2
-- name    : KeskinLiSong.DDPO.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:50:17.352658+00:00
-- url     : https://prove2.me/theorems/73d1c04d-fd9d-4374-98de-f38820094f37
-- title:
--   Theorem 2 — estimation contribution for both policies
-- statement:
--   Consider the model of Sections 2–3: real compact price and inventory intervals, an increasing C2 link, piecewise-constant demand parameters with C separated changes, independent centered locally light-tailed noise, and independent beta perishability. Costs satisfy the printed restriction. Estimators and policies are the concrete DDPO constructions, with measurable choices among genuine optimizers. Both policy branches are retained as one statement. The gap uses true-parameter unconstrained joint optimizers and the learner price and unconstrained inventory, not the implemented max-with-stock inventory. Each expected inclusive sum ranges over j=0,...,C and nonexperimental periods n*tau_plus_j+1 through n*tau_minus_j. The constants precede all T>=3.
--
--   $$
--   R_{\mathrm{est},N}(T)\le K_{15}T^{2/3}\sqrt{\log T},\qquad R_{\mathrm{est},E}(T)\le K_{16}\sqrt T\log T.
--   $$
--
--   The full source statement, including all definitions and clauses, is:
--
--   THEOREM 2. (a) For the DDPO-N policy, there exists a positive constant K_15 such that
--   E^π_{θ,ξ}[Σ_{j=0}^C Σ_{t=nτ̂_j^++1}^{nτ̂_j^−}
--    [Q(p_t^u,y_t^u;θ_t,ξ)−Q(p̂_t,ŷ_t^u;θ_t,ξ)]1{t∉𝒳}]
--    ≤ K_15 T^{2/3}(log T)^{1/2} for T = 3,4,...
--   (b) For the DDPO-E policy, there exists a positive constant K_16 such that
--   E^π_{θ,ξ}[Σ_{j=0}^C Σ_{t=nτ̂_j^++1}^{nτ̂_j^−}
--    [Q(p_t^u,y_t^u;θ_t,ξ,ϕ)−Q(p̂_t,ŷ_t^u;θ_t,ξ,ϕ)]1{t∉𝒳}]
--    ≤ K_16 T^{1/2} log T for T = 3,4,...
--
--   Differences from the source:
--   - reading: equation (6) uses alpha + beta p in the demand law → the law uses g(alpha + beta p); reason: equations (1) and (2) specify the general link; source finding I1
--   - encoding: expectations and probabilities under the observation law → coupled independent infinite primitive sequences with separate recursively generated policy histories; reason: the measurable history recursion induces the observation law and preserves every finite-horizon instance
--   - generalization: the surrounding model supposes an interior FIA optimum exists → this statement does not require an FIA existence premise; reason: adding that source premise specializes the statement; its estimators, proxies, derivatives or unconstrained-regret contributions do not use the FIA benchmark
--   - encoding: inclusive period sums with cycle-derived endpoints → finite inclusive sums intersected with periods 1 through T; reason: the process stops at T even if a change sentinel or cycle endpoint lies beyond T
--   - reading: the link g is increasing → g is nondecreasing and twice continuously differentiable; reason: increasing is read in its weak monotonicity sense; no strictly positive derivative or inverse-sensitivity assumption is printed
-- source:
--   Keskin, Li and Song (2022), Data-Driven Dynamic Pricing and Ordering with Perishable Inventory in a Changing Environment, Management Science, doi:10.1287/mnsc.2021.4011, supplied source.pdf (internally dated January 3, 2021; SSRN 3401188 footers), Theorem 2, printed p. 24 (PDF p. 24)

import Definitions.Def_KeskinLiSong_DDPO_Uniformity

open MeasureTheory ProbabilityTheory

namespace KeskinLiSong.DDPO

theorem theorem_2 (A : Model) (u : Tuning A) (d : ℕ) (F : ExponentialFamily d) :
    (∃ K15 : ℝ, 0 < K15 ∧
      ∀ (T : ℕ) (E : Environment A T) (L : Learner .nonparametric),
          3 ≤ T → Executes .nonparametric A u E L →
          ∀ opt : ℕ → Action,
            (∀ t ∈ Finset.Icc 1 T, JointOptimum A A.noise.law (E.theta t) E.xi (opt t)) →
            Integrable (contributionSample .estimation .nonparametric A u E L opt) (primitiveLaw A E) ∧
            contribution .estimation .nonparametric A u E L opt ≤ K15 * rate .N T) ∧
    ((NoiseMode.exponential d F).Fits A.noise.law →
      ∃ K16 : ℝ, 0 < K16 ∧
      ∀ (T : ℕ) (E : Environment A T) (L : Learner (.exponential d F)),
          3 ≤ T → Executes (.exponential d F) A u E L →
          ∀ opt : ℕ → Action,
            (∀ t ∈ Finset.Icc 1 T, JointOptimum A A.noise.law (E.theta t) E.xi (opt t)) →
            Integrable (contributionSample .estimation (.exponential d F) A u E L opt) (primitiveLaw A E) ∧
            contribution .estimation (.exponential d F) A u E L opt ≤ K16 * rate .E T) := by sorry

end KeskinLiSong.DDPO
