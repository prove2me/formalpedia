-- Prove2me | Theorems.Thm_KeskinLiSong_DDPO_theorem_1
-- name    : KeskinLiSong.DDPO.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:50:29.026855+00:00
-- url     : https://prove2.me/theorems/69738adf-8be4-4cec-8e42-e215cd662a7a
-- title:
--   Theorem 1 — regret bounds for both DDPO policies
-- statement:
--   Consider the model of Sections 2–3: real compact price and inventory intervals, an increasing C2 link, piecewise-constant demand parameters with C separated changes, independent centered locally light-tailed noise, and independent beta perishability. Costs satisfy the printed restriction. Estimators and policies are the concrete DDPO constructions, with measurable choices among genuine optimizers. There are measurable history-based learner rules for both versions, selected before the unknown noise law, number and separation of changes, and environment. For each fixed noise law, C, separation, public model bounds and tuning, positive finite K1,K2 precede every horizon T>=3 and every allowed change placement and parameter value. Whenever the source-assumed interior FIA optimum exists, the prescribed learner executes and every executing measurable optimizer selection has the asserted integrable regret. The exponential-family clause applies whenever the true noise law belongs to its specified family. In particular, T=4 and kappa=1 are retained; no valid-execution assumption hides the overlapping experimental assignments.
--
--   $$
--   \Delta_N(T)\le K_1T^{2/3}\sqrt{\log T},\qquad \Delta_E(T)\le K_2\sqrt T\log T\quad(T\ge3).
--   $$
--
--   The full source statement, including all definitions and clauses, is:
--
--   THEOREM 1. (a) For the DDPO-N policy, there exists a positive constant K_1 such that
--   Δ^π_{θ,ξ}(T) ≤ K_1 T^{2/3}(log T)^{1/2} for T = 3,4,... (18)
--   (b) For the DDPO-E policy, there exists a positive constant K_2 such that
--   Δ^π_{θ,ξ}(T) ≤ K_2 T^{1/2} log T for T = 3,4,... (19)
--
--   Differences from the source:
--   - reading: equation (6) uses alpha + beta p in the demand law → the law uses g(alpha + beta p); reason: equations (1) and (2) specify the general link; source finding I1
--   - encoding: expectations and probabilities under the observation law → coupled independent infinite primitive sequences with separate recursively generated policy histories; reason: the measurable history recursion induces the observation law and preserves every finite-horizon instance
--   - encoding: the named policy, optimizer or estimator is used as a defined mathematical object → operational existence, integrability and genuine attainment are explicit content where required; reason: partial constructions are not silently filled by arbitrary defaults or assumed as a premise of the goal
--   - encoding: the learner does not know the disturbance law, change count or change parameters → learner rules are quantified before those unknowns, while each rate constant is after fixed model data and before all horizons; reason: this makes the operational and horizon-uniform meaning explicit without a valid-execution premise
--   - reading: the link g is increasing → g is nondecreasing and twice continuously differentiable; reason: increasing is read in its weak monotonicity sense; no strictly positive derivative or inverse-sensitivity assumption is printed
-- source:
--   Keskin, Li and Song (2022), Data-Driven Dynamic Pricing and Ordering with Perishable Inventory in a Changing Environment, Management Science, doi:10.1287/mnsc.2021.4011, supplied source.pdf (internally dated January 3, 2021; SSRN 3401188 footers), Theorem 1, printed p. 12 (PDF p. 12)

import Definitions.Def_KeskinLiSong_DDPO_Uniformity

namespace KeskinLiSong.DDPO

theorem theorem_1 (A : Model) (u : Tuning A) (d : ℕ) (F : ExponentialFamily d) :
    ∃ (algorithmN : ℕ → Learner .nonparametric)
      (algorithmE : ℕ → Learner (.exponential d F)),
    ∀ (noise : LocalMGF) (C : ℕ) (delta : ℝ) (hdelta : 0 < delta),
      let B := instanceWith A noise C delta hdelta
      let v := retune A u noise C delta hdelta
      (∃ K1 : ℝ, 0 < K1 ∧ Performance .nonparametric B v algorithmN K1) ∧
      ((NoiseMode.exponential d F).Fits noise.law →
        ∃ K2 : ℝ, 0 < K2 ∧ Performance (.exponential d F) B v algorithmE K2) := by sorry

end KeskinLiSong.DDPO
