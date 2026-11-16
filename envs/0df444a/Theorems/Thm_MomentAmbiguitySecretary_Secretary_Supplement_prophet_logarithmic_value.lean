-- Prove2me | Theorems.Thm_MomentAmbiguitySecretary_Secretary_Supplement_prophet_logarithmic_value
-- name    : MomentAmbiguitySecretary.Secretary.Supplement.prophet_logarithmic_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:57:44.041165+00:00
-- url     : https://prove2.me/theorems/637597f9-79c6-4997-9ab5-ee13988d7c7d
-- title:
--   Theorem 7.1 (companion theorem; not used in the proof of the goal) — Both logarithmic bounds on the full moment-based randomized single-choice competitive value for every fixed order statistic
-- statement:
--   Fix any integer $r\ge1$. Let $\rho_{m,r}^{\mathrm{mom}}$ be the supremum of all $\alpha\ge0$ for which one measurable randomized moment-based policy guarantees
--   $$\mathbb E[Z_\tau]\ge\alpha\,\mathbb E[Z_{(r)}]$$
--   for every length-$m$ independent nonnegative all-moment instance. Values arrive in fixed index order, $Z_{(r)}$ is the $r$-th largest with ties retained, and no selection earns zero. There exist $a_r,b_r>0$ and an integer $m_0(r)\ge\max(r,2)$ such that, for every $m\ge m_0(r)$,
--   $$\frac{a_r}{\log m}\le\rho_{m,r}^{\mathrm{mom}}\le\frac{b_r}{\log m}.$$
--   The logarithm is natural. Constants precede the horizon. The achievable set is also asserted nonempty and bounded, making the real supremum well posed. Policies depend on the realizable full moment disclosures and observed prefixes; a causal subprobability selection kernel represents arbitrary independent private randomization. The cited lower bound is a proof obligation, not a hypothesis.
--
--   Differences from the source:
--   - encoding: supremum of achievable nonnegative guarantees over randomized single-choice policies → causal subprobability kernels and an explicitly nonempty bounded achievable set; reason: kernels realize exactly the same randomized stopping decisions using independent private uniforms; zero policy gives 0 and the all-one instance bounds coefficients by 1
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied checksum-pinned preprint. Theorem 7.1, PDF/printed p.18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf; SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Supplement_Prophet

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace MomentAmbiguitySecretary.Secretary.Supplement

/-- Theorem 7.1, supplied preprint, PDF/printed p.18. -/
theorem prophet_logarithmic_value (r : ℕ) (hr : 1 ≤ r) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ m₀ : ℕ, max r 2 ≤ m₀ ∧
      ∀ m : ℕ, m₀ ≤ m →
        (achievable m r).Nonempty ∧ BddAbove (achievable m r) ∧
        a / Real.log (m : ℝ) ≤ prophetValue m r ∧
        prophetValue m r ≤ b / Real.log (m : ℝ) := by sorry

end MomentAmbiguitySecretary.Secretary.Supplement
