-- Prove2me | Theorems.Thm_InfoRelaxTS_Asymptotic_proposition_1
-- name    : InfoRelaxTS.Asymptotic.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:22.863296+00:00
-- url     : https://prove2.me/theorems/e45729f2-16db-4878-a2b6-be8cc497750c
-- title:
--   Proposition 1, p. 25 — as T → ∞ the action laws of IRS.FH and IRS.V-Zero converge to that of Thompson sampling
-- statement:
--   Consider the Bayesian bandit model with $K \ge 1$ arms, a conjugate prior family $\{\mathcal P_a(y_a)\}$ with a measurable Bayesian update, and rewards satisfying the standing integrability assumption (3). Fix a belief vector $y$ and assume that the conditional mean rewards of distinct arms differ almost surely under the prior:
--   $$\mu_i(\theta_i) \ne \mu_j(\theta_j) \quad \mathcal P(y)\text{-almost surely, for all } i \ne j.$$
--   The three actions are random variables, each policy using a randomly sampled outcome of its own:
--   1. $A^{TS}(y)$, the action of Thompson sampling, samples $\tilde\theta \sim \mathcal P(y)$ and plays $\operatorname{argmax}_a \mu_a(\tilde\theta_a)$;
--   2. $A^{IRS.FH}(T, y)$, the action of IRS.FH at remaining horizon $T$, samples $\tilde\omega \sim \mathcal I(y)$ and plays $\operatorname{argmax}_a \hat\mu_{a,T-1}(\tilde\omega)$;
--   3. $A^{IRS.V\text{-}Zero}(T, y)$, the action of IRS.V-Zero, samples $\tilde\omega \sim \mathcal I(y)$, computes an optimal allocation $\tilde n^* \in \mathcal N_T$ of the inner problem $\max_{n \in \mathcal N_T} \sum_a \sum_{i=1}^{n_a} \hat\mu_{a,i-1}(\tilde\omega)$ (37), and plays $\operatorname{argmax}_a \tilde n^*_a$.
--
--   The ties in every argmax and in the inner problem are broken by arbitrary measurable rules. Then, for every arm $a \in \mathcal A$,
--   $$\lim_{T\to\infty} \mathbb P\big[A^{IRS.FH}(T, y) = a\big] = \mathbb P\big[A^{TS}(y) = a\big] \quad (55), \qquad \lim_{T\to\infty} \mathbb P\big[A^{IRS.V\text{-}Zero}(T, y) = a\big] = \mathbb P\big[A^{TS}(y) = a\big] \quad (56).$$
--
--   So both IRS policies start a long horizon by randomizing exactly as Thompson sampling does. They become myopic only as the remaining horizon shrinks (Remark 5 of the paper).
--
--   **Formalization Note.** $\mathbb P[A = a]$ is the mass of $\{a\}$ under the pushforward of the policy's sampling law by its arm-selection map, converted to a real number. The conclusion holds for every choice of the four tie-breaking rules: one each for the argmaxes of TS, IRS.FH and IRS.V-Zero, and one for the optimal allocation, which may depend on the horizon and on the payoff table. All four are required to be measurable so that the pushforwards are probability measures. Footnote 8's selection rule $\operatorname{argmax}_a \tilde n^*_a$ is built in. The posterior means are the conjugate (pathwise) version of (10), see the Setting definition. Conjugacy, the measurability of the update and (3) are the standing assumptions of §2.1. $K \ge 1$ is needed for the argmax to exist.
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, p. 25, Proposition 1, (55)–(56) and footnote 8

import Mathlib
import Definitions.Def_InfoRelaxTS_Asymptotic_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace InfoRelaxTS.Asymptotic

/-- Proposition 1 (p. 25): as `T → ∞`, the laws of the actions of IRS.FH (55) and of IRS.V-Zero
(56) converge to the law of the action of Thompson sampling, for every tie-breaking rule. -/
theorem proposition_1 {K : ℕ} [NeZero K] {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hU : ∀ a, Measurable (Function.uncurry (U a)))
    (hconj : IsConjugate R P U) (hint : RewardsIntegrable R P) (y : Fin K → Y)
    (hdistinct : ∀ i j : Fin K, i ≠ j → ∀ᵐ θ ∂(priorLaw P y), Monotone.mu R i (θ i) ≠ Monotone.mu R j (θ j))
    (selTS : (Fin K → ℝ) → Fin K) (hselTS : Gap.IsArgmaxSel selTS) (hselTSm : Measurable selTS)
    (selFH : (Fin K → ℝ) → Fin K) (hselFH : Gap.IsArgmaxSel selFH) (hselFHm : Measurable selFH)
    (selVZ : (Fin K → ℝ) → Fin K) (hselVZ : Gap.IsArgmaxSel selVZ) (hselVZm : Measurable selVZ)
    (asel : ℕ → (Fin K → ℕ → ℝ) → (Fin K → ℕ)) (hasel : Gap.IsOptAllocSel asel)
    (haselm : ∀ T, Measurable (asel T)) :
    ∀ a : Fin K,
      Tendsto (fun T : ℕ => (fhLaw R P U selFH T y {a}).toReal) atTop
          (𝓝 (tsLaw R P selTS y {a}).toReal) ∧
        Tendsto (fun T : ℕ => (vzLaw R P U asel selVZ T y {a}).toReal) atTop
          (𝓝 (tsLaw R P selTS y {a}).toReal) := by sorry

end InfoRelaxTS.Asymptotic
