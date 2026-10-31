-- Prove2me | Theorems.Thm_KeskinLiSong_DDPO_proposition_8
-- name    : KeskinLiSong.DDPO.proposition_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:51:21.490973+00:00
-- url     : https://prove2.me/theorems/f8fa14bb-8481-43bb-a1aa-bc8ebf4574e5
-- title:
--   Proposition 8 — late detections and early false alarms
-- statement:
--   Consider the model of Sections 2–3: real compact price and inventory intervals, an increasing C2 link, piecewise-constant demand parameters with C separated changes, independent centered locally light-tailed noise, and independent beta perishability. Costs satisfy the printed restriction. Estimators and policies are the concrete DDPO constructions, with measurable choices among genuine optimizers. All four bounds are retained, with independent positive constants K17 through K20. Delay intervals run from n*tau*_j+1 through n*tau_plus_j. False-alarm intervals use n*tau_minus_j+1 through n*tau*_(j+1), the intended lower endpoint printed in the final proof. The two false-alarm bounds are K19 sqrt T and K20 sqrt T, without an added logarithm.
--
--   $$
--   R_{\mathrm{delay},N}(T)\le K_{17}T^{2/3}\sqrt{\log T},\quad R_{\mathrm{delay},E}(T)\le K_{18}\sqrt T\log T,\qquad R_{\mathrm{false},N}(T)\le K_{19}\sqrt T,\quad R_{\mathrm{false},E}(T)\le K_{20}\sqrt T.
--   $$
--
--   The full source statement, including all definitions and clauses, is:
--
--   PROPOSITION 8. (a) (Delay of True Detections) For the DDPO-N policy, there exists a positive constant
--   K_17 such that
--   E^π_{θ,ξ}[Σ_{j=0}^C Σ_{t=nτ*_j+1}^{nτ̂_j^+}
--    [Q(p_t^u,y_t^u;θ_t,ξ)−Q(p̂_t,ŷ_t^u;θ_t,ξ)]1{t∉𝒳}]
--    ≤ K_17 T^{2/3}(log T)^{1/2} for T = 3,4,...
--   For the DDPO-E policy, there exists a positive constant K_18 such that
--   E^π_{θ,ξ}[Σ_{j=0}^C Σ_{t=nτ*_j+1}^{nτ̂_j^+}
--    [Q(p_t^u,y_t^u;θ_t,ξ,ϕ)−Q(p̂_t,ŷ_t^u;θ_t,ξ,ϕ)]1{t∉𝒳}]
--    ≤ K_18 T^{1/2} log T for T = 3,4,...
--   (b) (Early False Alarms) For the DDPO-N policy, there exists a positive constant K_19 such that
--   E^π_{θ,ξ}[Σ_{j=0}^C Σ_{t=τ̂_j^−+1}^{nτ*_{j+1}}
--    [Q(p_t^u,y_t^u;θ_t,ξ)−Q(p̂_t,ŷ_t^u;θ_t,ξ)]1{t∉𝒳}]
--    ≤ K_19 T^{1/2} for T = 3,4,...
--   For the DDPO-E policy, there exists a positive constant K_20 such that
--   E^π_{θ,ξ}[Σ_{j=0}^C Σ_{t=τ̂_j^−+1}^{nτ*_{j+1}}
--    [Q(p_t^u,y_t^u;θ_t,ξ,ϕ)−Q(p̂_t,ŷ_t^u;θ_t,ξ,ϕ)]1{t∉𝒳}]
--    ≤ K_20 T^{1/2} for T = 3,4,...
--
--   Differences from the source:
--   - reading: equation (6) uses alpha + beta p in the demand law → the law uses g(alpha + beta p); reason: equations (1) and (2) specify the general link; source finding I1
--   - encoding: expectations and probabilities under the observation law → coupled independent infinite primitive sequences with separate recursively generated policy histories; reason: the measurable history recursion induces the observation law and preserves every finite-horizon instance
--   - generalization: the surrounding model supposes an interior FIA optimum exists → this statement does not require an FIA existence premise; reason: adding that source premise specializes the statement; its estimators, proxies, derivatives or unconstrained-regret contributions do not use the FIA benchmark
--   - encoding: inclusive period sums with cycle-derived endpoints → finite inclusive sums intersected with periods 1 through T; reason: the process stops at T even if a change sentinel or cycle endpoint lies beyond T
--   - reading: part (b) prints tau_minus_j+1 → the lower limit is n*tau_minus_j+1; reason: the final decomposition on ec19 explicitly includes n; source finding I5
--   - reading: the link g is increasing → g is nondecreasing and twice continuously differentiable; reason: increasing is read in its weak monotonicity sense; no strictly positive derivative or inverse-sensitivity assumption is printed
-- source:
--   Keskin, Li and Song (2022), Data-Driven Dynamic Pricing and Ordering with Perishable Inventory in a Changing Environment, Management Science, doi:10.1287/mnsc.2021.4011, supplied source.pdf (internally dated January 3, 2021; SSRN 3401188 footers), Proposition 8, printed p. 24–25 (PDF p. 24)

import Definitions.Def_KeskinLiSong_DDPO_Uniformity

open MeasureTheory ProbabilityTheory

namespace KeskinLiSong.DDPO

theorem proposition_8 (A : Model) (u : Tuning A) (d : ℕ) (F : ExponentialFamily d) :
    (∃ K17 : ℝ, 0 < K17 ∧
      ∀ (T : ℕ) (E : Environment A T) (L : Learner .nonparametric),
          3 ≤ T → Executes .nonparametric A u E L →
          ∀ opt : ℕ → Action,
            (∀ t ∈ Finset.Icc 1 T, JointOptimum A A.noise.law (E.theta t) E.xi (opt t)) →
            Integrable (contributionSample .delay .nonparametric A u E L opt) (primitiveLaw A E) ∧
            contribution .delay .nonparametric A u E L opt ≤ K17 * rate .N T) ∧
    ((NoiseMode.exponential d F).Fits A.noise.law →
      ∃ K18 : ℝ, 0 < K18 ∧
      ∀ (T : ℕ) (E : Environment A T) (L : Learner (.exponential d F)),
          3 ≤ T → Executes (.exponential d F) A u E L →
          ∀ opt : ℕ → Action,
            (∀ t ∈ Finset.Icc 1 T, JointOptimum A A.noise.law (E.theta t) E.xi (opt t)) →
            Integrable (contributionSample .delay (.exponential d F) A u E L opt) (primitiveLaw A E) ∧
            contribution .delay (.exponential d F) A u E L opt ≤ K18 * rate .E T) ∧
    (∃ K19 : ℝ, 0 < K19 ∧
      ∀ (T : ℕ) (E : Environment A T) (L : Learner .nonparametric),
          3 ≤ T → Executes .nonparametric A u E L →
          ∀ opt : ℕ → Action,
            (∀ t ∈ Finset.Icc 1 T, JointOptimum A A.noise.law (E.theta t) E.xi (opt t)) →
            Integrable (contributionSample .falseAlarm .nonparametric A u E L opt) (primitiveLaw A E) ∧
            contribution .falseAlarm .nonparametric A u E L opt ≤ K19 * Real.sqrt T) ∧
    ((NoiseMode.exponential d F).Fits A.noise.law →
      ∃ K20 : ℝ, 0 < K20 ∧
      ∀ (T : ℕ) (E : Environment A T) (L : Learner (.exponential d F)),
          3 ≤ T → Executes (.exponential d F) A u E L →
          ∀ opt : ℕ → Action,
            (∀ t ∈ Finset.Icc 1 T, JointOptimum A A.noise.law (E.theta t) E.xi (opt t)) →
            Integrable (contributionSample .falseAlarm (.exponential d F) A u E L opt) (primitiveLaw A E) ∧
            contribution .falseAlarm (.exponential d F) A u E L opt ≤ K20 * Real.sqrt T) := by sorry

end KeskinLiSong.DDPO
