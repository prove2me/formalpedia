-- Prove2me | Theorems.Thm_InfoRelaxTS_Monotone_Supplement_proposition_3
-- name    : InfoRelaxTS.Monotone.Supplement.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:56:14.637518+00:00
-- url     : https://prove2.me/theorems/a1a9dd5b-87af-4e49-b84e-da966eb0d528
-- title:
--   Proposition 3, p. 50 — mean equivalence: a dual feasible penalty does not change the performance of a non-anticipating policy
-- statement:
--   Consider the Bayesian bandit of §2.1 with $K$ arms, reward laws $\mathcal R_a(\theta_a)$, conjugate priors $\mathcal P_a(y_a)$ and Bayesian update $\mathcal U_a$, under its standing assumptions: $\mathcal U_a(y_a,r)$ is the Bayes posterior after observing $r$, the update maps are measurable, and $\mathbb E_{y_a}|R_{a,1}|<\infty$ for every belief $y_a$ (3). Fix a horizon $T$ and a prior $y$, and let $z_t(a_{1:t},\omega)$ be a dual feasible penalty: for every non-anticipating policy the total penalty has a finite expectation equal to $0$ (Definition 1).
--
--   Then for every non-anticipating policy $\pi\in\Pi_{\mathbb F}$, including randomized and history-dependent ones, the total reward and the penalized total reward are integrable and
--
--   $$\mathbb E^\pi_y\Big[\sum_{t=1}^T r_t(A^\pi_{1:t},\omega)-z_t(A^\pi_{1:t},\omega)\Big]=\mathbb E^\pi_y\Big[\sum_{t=1}^T r_t(A^\pi_{1:t},\omega)\Big]=V(\pi,T,y).$$
--
--   Penalties that are fair to every non-anticipating policy leave the value of every such policy unchanged; this is the first step of weak duality in Theorem 1.
--
--   **Formalization Note** Policies are a private seed with a probability law, independent of $\omega$, and jointly measurable decision rules on the seed and the rewards observed so far; arms and times are 0-based. The integrability of both totals is stated as part of the conclusion so that neither expectation is a default value.
--
--   Differences from the source:
--   - encoding: arms 1..K, times 1..T, rewards R_{a,n} → `Fin K`, `Fin T`, `(ω a).2 (n - 1)`; reason: 0-based Lean indexing, same instances
--   - reading: non-anticipating policies including randomized ones → a private seed with a probability law independent of ω and jointly measurable rules of the seed and the observed rewards; reason: an F_{t-1}-measurable action with private randomization is a measurable function of the seed and the past rewards (the past actions are functions of these)
--   - reading: dual feasibility (18), zero expected total penalty → the total penalty is integrable under every policy's law and its integral is 0; reason: (18) asserts an expectation equals 0, which presupposes that it exists
--   - reading: equality (83) of two expectations → also concludes that the total reward and the penalized total reward are integrable; reason: the expectations in (83) are finite under (3) and Definition 1, and stating this rules out a default value of the integral
--   - generalization: stochastic penalty functions z_t in §3 → arbitrary real prefix-dependent summands, requiring only integrability and zero mean of the total penalty along every policy; reason: individual summands may cancel even when they are not measurable or integrable; deterministic policies give integrable totals for every fixed action sequence, and their finite maximum is integrable, so the source claim is preserved
--   - generalization: positive finite horizons in the theorem statements → all natural horizons, including T = 0; reason: the empty total reward, total penalty, inner value and Bellman value are all zero, so the conclusion extends to the terminal boundary
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, p. 50, Proposition 3, (83)

import Mathlib
import Definitions.Def_InfoRelaxTS_Monotone_Setting
import Definitions.Def_InfoRelaxTS_Monotone_Supplement_Duality

namespace InfoRelaxTS.Monotone.Supplement

open MeasureTheory ProbabilityTheory InfoRelaxTS.Monotone

/-- Proposition 3 (mean equivalence), p. 50, (83): if the penalty `z` is dual feasible, then for
every non-anticipating (possibly randomized) policy `π` the expected penalized total reward is
well defined and equals the expected total reward `V(π, T, y)`, which is itself well defined. -/
theorem proposition_3 {K : ℕ} {Θ Y : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    [Nonempty Θ] [MeasurableSpace Y]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : StandingAssumptions R P U)
    (T : ℕ) (y : Fin K → Y) (z : Penalty K Θ) (hz : DualFeasible R P z T y) (π : Policy K) :
    Integrable (fun p => π.totalReward T p.1 p.2) (π.law R P y) ∧
      Integrable (fun p => ∑ t : Fin T,
        (rew (π.path p.1 p.2 T) t p.2 - z t (pre (π.path p.1 p.2 T) t) p.2)) (π.law R P y) ∧
      ∫ p, (∑ t : Fin T,
        (rew (π.path p.1 p.2 T) t p.2 - z t (pre (π.path p.1 p.2 T) t) p.2)) ∂(π.law R P y)
        = V R P π T y := by sorry

end InfoRelaxTS.Monotone.Supplement
