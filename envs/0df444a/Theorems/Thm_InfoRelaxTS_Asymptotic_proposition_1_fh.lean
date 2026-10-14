-- Prove2me | Theorems.Thm_InfoRelaxTS_Asymptotic_proposition_1_fh
-- name    : InfoRelaxTS.Asymptotic.proposition_1_fh
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:31.131463+00:00
-- url     : https://prove2.me/theorems/5d32b797-ed79-4955-83d7-65bc26caab20
-- title:
--   Proposition 1, (55), p. 25 — as T → ∞ the action law of IRS.FH converges to that of Thompson sampling
-- statement:
--   Consider the Bayesian bandit model with $K \ge 1$ arms, a conjugate prior family $\{\mathcal P_a(y_a)\}$ with a measurable Bayesian update, and rewards satisfying the standing integrability assumption (3). Fix a belief vector $y$. Assume that the conditional mean rewards of distinct arms differ almost surely under the prior:
--   $$\mu_i(\theta_i) \ne \mu_j(\theta_j) \quad \mathcal P(y)\text{-almost surely, for all } i \ne j.$$
--   Let $A^{TS}(y)$ be the action of Thompson sampling (sample $\tilde\theta \sim \mathcal P(y)$ and play $\operatorname{argmax}_a \mu_a(\tilde\theta_a)$). Let $A^{IRS.FH}(T,y)$ be the action of IRS.FH at remaining horizon $T$ (sample $\tilde\omega \sim \mathcal I(y)$ and play $\operatorname{argmax}_a \hat\mu_{a,T-1}(\tilde\omega)$). Each argmax is taken by an arbitrary measurable tie-breaking rule, possibly a different one for each policy. Then
--   $$\lim_{T\to\infty} \mathbb P\big[A^{IRS.FH}(T, y) = a\big] = \mathbb P\big[A^{TS}(y) = a\big] \qquad \forall a \in \mathcal A.$$
--
--   This is display (55) of Proposition 1 on its own. It says that IRS.FH, which looks ahead $T-1$ rewards per arm, behaves like Thompson sampling at the start of a long horizon.
--
--   **Formalization Note.** $\mathbb P[A = a]$ is the mass of $\{a\}$ under the pushforward of the policy's sampling law by its arm-selection map, converted to a real number. The tie-breaking rules are required to be measurable so that these pushforwards are probability measures. The posterior means are the conjugate (pathwise) version of (10), see the Setting definition. Conjugacy, the measurability of the update and (3) are the standing assumptions of §2.1. $K \ge 1$ is needed for the argmax to exist.
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, p. 25, Proposition 1, (55)

import Mathlib
import Definitions.Def_InfoRelaxTS_Asymptotic_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace InfoRelaxTS.Asymptotic

/-- Proposition 1, (55) (p. 25): as `T → ∞`, the law of the action of IRS.FH converges to the law
of the action of Thompson sampling, for every tie-breaking rule of either policy. -/
theorem proposition_1_fh {K : ℕ} [NeZero K] {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hU : ∀ a, Measurable (Function.uncurry (U a)))
    (hconj : IsConjugate R P U) (hint : RewardsIntegrable R P) (y : Fin K → Y)
    (hdistinct : ∀ i j : Fin K, i ≠ j → ∀ᵐ θ ∂(priorLaw P y), Monotone.mu R i (θ i) ≠ Monotone.mu R j (θ j))
    (selTS : (Fin K → ℝ) → Fin K) (hselTS : Gap.IsArgmaxSel selTS) (hselTSm : Measurable selTS)
    (selFH : (Fin K → ℝ) → Fin K) (hselFH : Gap.IsArgmaxSel selFH) (hselFHm : Measurable selFH) :
    ∀ a : Fin K, Tendsto (fun T : ℕ => (fhLaw R P U selFH T y {a}).toReal) atTop
      (𝓝 (tsLaw R P selTS y {a}).toReal) := by sorry

end InfoRelaxTS.Asymptotic
