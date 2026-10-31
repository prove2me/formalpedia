-- Prove2me | Theorems.Thm_KeskinLiSong_DDPO_proposition_1
-- name    : KeskinLiSong.DDPO.proposition_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:51:10.288725+00:00
-- url     : https://prove2.me/theorems/c5ada3b5-8c1e-49ad-a4e1-6337be095bf6
-- title:
--   Proposition 1 — FIA versus FINA
-- statement:
--   Consider the model of Sections 2–3: real compact price and inventory intervals, an increasing C2 link, piecewise-constant demand parameters with C separated changes, independent centered locally light-tailed noise, and independent beta perishability. Costs satisfy the printed restriction. Estimators and policies are the concrete DDPO constructions, with measurable choices among genuine optimizers. The constant Ñ precedes every positive horizon and allowed environment. Q̄′ is an attained maximum of the Euclidean gradient norm over the action rectangle and active demand regimes; existence of those gradients is explicit content, not an extra premise. The exact diameter is sqrt((p_max-p_min)^2+(y_max-y_min)^2). FIA and FINA have separate stock paths.
--
--   $$
--   \mathbb E\sum_{t=1}^{T}\bigl[Q(p_t^*,y_t^*)-Q(\check p_t,\check y_t)\bigr]\le 2\overline Q^{\prime}\,\operatorname{diam}(P\times Y)(\widetilde N+1)(C+1).
--   $$
--
--   The full source statement, including all definitions and clauses, is:
--
--   PROPOSITION 1. There exists a positive constant Ñ such that
--   E^π_{θ,ξ}[Σ_{t=1}^T [Q(p*_t,y*_t;θ_t,ξ)−Q(p̌_t,y̌_t;θ_t,ξ)]]
--    ≤ 2 Q̄′ d̄(P×Y)(Ñ+1)(C+1) (22)
--   for all T = 1,2,..., where Q̄′ = max{‖∇Q(p,y)‖ : p∈P,y∈Y} and d̄(P×Y) is the maximum
--   distance between two points in P×Y.
--
--   Differences from the source:
--   - reading: equation (6) uses alpha + beta p in the demand law → the law uses g(alpha + beta p); reason: equations (1) and (2) specify the general link; source finding I1
--   - encoding: expectations and probabilities under the observation law → coupled independent infinite primitive sequences with separate recursively generated policy histories; reason: the measurable history recursion induces the observation law and preserves every finite-horizon instance
--   - encoding: the named policy, optimizer or estimator is used as a defined mathematical object → operational existence, integrability and genuine attainment are explicit content where required; reason: partial constructions are not silently filled by arbitrary defaults or assumed as a premise of the goal
--   - reading: Q̄′ suppresses the demand-regime argument → the maximum ranges over the action rectangle and the active demand regimes; reason: one bound must cover every term of the displayed time sum; this is the uniform-gradient reading of the suppressed parameters
--   - reading: the link g is increasing → g is nondecreasing and twice continuously differentiable; reason: increasing is read in its weak monotonicity sense; no strictly positive derivative or inverse-sensitivity assumption is printed
-- source:
--   Keskin, Li and Song (2022), Data-Driven Dynamic Pricing and Ordering with Perishable Inventory in a Changing Environment, Management Science, doi:10.1287/mnsc.2021.4011, supplied source.pdf (internally dated January 3, 2021; SSRN 3401188 footers), Proposition 1, printed p. 21 (PDF p. 21)

import Definitions.Def_KeskinLiSong_DDPO_Uniformity

open MeasureTheory ProbabilityTheory Set

namespace KeskinLiSong.DDPO

theorem proposition_1 (A : Model) :
    ∃ Ntilde : ℝ, 0 < Ntilde ∧ ∀ T : ℕ, 1 ≤ T →
      ∀ E : Environment A T, HasFIA A E →
      (∃ myopic : Policy, FINA A E myopic) ∧
      ∀ benchmark myopic : Policy, FIA A E benchmark → FINA A E myopic →
      (∀ t ∈ Finset.Icc 1 T, ∀ a : Vector 2, a 0 ∈ A.P → a 1 ∈ A.Y →
        DifferentiableAt ℝ (fun z : Vector 2 => Q A A.noise.law (E.theta t) E.xi (z 0) (z 1)) a) ∧
      ∃ Qprime : ℝ,
        IsGreatest {r | ∃ t ∈ Finset.Icc 1 T, ∃ a : Vector 2,
          a 0 ∈ A.P ∧ a 1 ∈ A.Y ∧
          r = ‖fderiv ℝ (fun z : Vector 2 => Q A A.noise.law (E.theta t) E.xi (z 0) (z 1)) a‖}
          Qprime ∧
        Integrable (regretSample A E benchmark myopic) (primitiveLaw A E) ∧
        regret A E benchmark myopic ≤
          2 * Qprime * Real.sqrt ((A.pmax - A.pmin) ^ 2 + (A.ymax - A.ymin) ^ 2) *
            (Ntilde + 1) * (A.changes + 1) := by sorry

end KeskinLiSong.DDPO
