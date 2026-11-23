-- Prove2me | Theorems.Thm_InfoRelaxTS_Monotone_Supplement_theorem_1
-- name    : InfoRelaxTS.Monotone.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:56:59.567897+00:00
-- url     : https://prove2.me/theorems/867c5de9-c802-4dec-a322-19eb59f8c735
-- title:
--   Theorem 1 (corrected: indexing of V* in (16)), p. 11 — weak duality W^z ≥ V*, and the ideal penalty (22) is dual feasible with W^ideal = V*
-- statement:
--   Consider the Bayesian bandit of §2.1 with $K\ge1$ arms, reward laws $\mathcal R_a(\theta_a)$, conjugate priors $\mathcal P_a(y_a)$ and Bayesian update $\mathcal U_a$, under its standing assumptions: $\mathcal U_a(y_a,r)$ is the Bayes posterior after observing $r$, the update maps are measurable, and $\mathbb E_{y_a}|R_{a,1}|<\infty$ for every belief $y_a$ (3). Fix a horizon $T$ and a prior $y$. Let $V^*$ be the Bayesian optimal value of (15)–(16), $V(\pi,T,y)$ the performance (7) of a non-anticipating policy $\pi\in\Pi_{\mathbb F}$, and for a penalty $z$ let
--
--   $$W^z(T,y)=\mathbb E_y\Big[\max_{a_{1:T}\in\mathcal A^T}\sum_{t=1}^T r_t(a_{1:t},\omega)-z_t(a_{1:t},\omega;T,y)\Big]$$
--
--   be the expected value of the inner problem (19). Then:
--
--   1. **(Weak duality, (20))** If $z$ is dual feasible, the inner maximum is integrable and $W^z(T,y)\ge V(\pi,T,y)$ for every $\pi\in\Pi_{\mathbb F}$; in particular $W^z(T,y)\ge V^*(T,y)$.
--   2. The ideal penalty
--   $$z^{\rm ideal}_t(a_{1:t},\omega;T,y)=r_t(a_{1:t},\omega)-\mathbb E_y[r_t(a_{1:t},\omega)\mid H_{t-1}(a_{1:t-1},\omega)]+V^*(T-t,y_t(a_{1:t},\omega;y))-\mathbb E_y\big[V^*(T-t,y_t(a_{1:t},\omega;y))\mid H_{t-1}(a_{1:t-1},\omega)\big]$$
--   of (22) is dual feasible.
--   3. **(Strong duality, (21))** $W^{\rm ideal}(T,y)=V^*(T,y)$.
--   4. $V^*(T,y)$ is the supremum of $V(\pi,T,y)$ over $\pi\in\Pi_{\mathbb F}$, as in (17), so the optimal value in (20)–(21) can be read either as the Bellman value or as the best performance of a non-anticipating policy.
--
--   Items 2 and 3 give the dual feasible penalty attaining equality whose existence the theorem asserts. Unlike the ideal penalty of Brown, Smith and Sun (2010), (22) also centres the reward itself, because bandit rewards are random given the history.
--
--   **Formalization Note** Arms and times are 0-based. Policies are a private seed with a probability law, independent of $\omega$, and jointly measurable decision rules on the seed and the observed rewards. The two conditional expectations in (22) are taken in their conjugate predictive versions, $\bar\mu_{a_t}([y_{t-1}]_{a_t})$ and the predictive expectation of $V^*(T-t,\mathcal U(y_{t-1},a_t,R))$, so the ideal penalty is defined at every outcome. $V^*$ is defined by the Bellman recursion with the consistent indexing $V^*(T,y)=\max_a Q^*(T,y,a)$.
--
--   Differences from the source:
--   - encoding: arms 1..K, times 1..T, rewards R_{a,n}, V*(T − t, ·) at time t → `Fin K`, `Fin T`, `(ω a).2 (n - 1)`, `Vstar (T - t - 1)` at Lean time t; reason: 0-based Lean indexing, same instances
--   - encoding: the paper never states K ≥ 1 → `[NeZero K]`; reason: max_a over 𝒜 in (16) and (19) requires a nonempty arm set; excludes only the undefined case K = 0
--   - correction: (16) V*(T, y) = max_a Q*(T − 1, y, a) → V*(T + 1, y) = max_a E_{y_a}[R_{a,1} + V*(T, U(y, a, R_{a,1}))], i.e. V*(T, y) = max_a Q*(T, y, a); reason: printed off-by-one; (15), Algorithm 1 (p. 8), (89)–(90) and (100) (pp. 51–52) all use V*(T, y) = max_a Q*(T, y, a), and the printed (16) would make V*(1, y) depend on Q*(0, ·); no case is excluded
--   - reading: non-anticipating policies including randomized ones → a private seed with a probability law independent of ω and jointly measurable rules of the seed and the observed rewards; reason: an F_{t-1}-measurable action with private randomization is a measurable function of the seed and the past rewards
--   - reading: dual feasibility (18) → the total penalty is integrable under every policy's law and its integral is 0; reason: (18) asserts an expectation equals 0, which presupposes that it exists
--   - reading: the conditional expectations E_y[· | H_{t−1}] in (22) → their conjugate predictive versions μ̄_{a_t}([y_{t−1}]_{a_t}) and ∫ V*(T − t, U(y_{t−1}, a_t, r)) d pred_{a_t}([y_{t−1}]_{a_t})(r); reason: conditional expectations are defined only almost surely; by the conjugacy assumption these are versions, and a pointwise version is needed for the pathwise inner problem (*), as in the proof (92)–(95)
--   - reading: V* the optimal value → V* is the Bellman value (15)–(16), weak duality is also stated against every policy, and the conclusion adds that V* is the supremum of V(π, T, y) over Π_F (17); reason: the theorem calls V* the optimal value and (17) identifies the two readings, so both are covered
--   - reading: "there exists a dual feasible penalty z^ideal with W^ideal = V*, of the form (22)" → the specific penalty (22) is dual feasible and W^ideal = V*; reason: this is the existence claim with its witness, which the theorem names
--   - reading: weak duality W^z ≥ V* → also concludes that the inner maximum is integrable; reason: makes W^z a genuine expectation rather than a default value
--   - generalization: stochastic penalty functions z_t in §3 → arbitrary real prefix-dependent summands, requiring only integrability and zero mean of the total penalty along every policy; reason: individual summands may cancel even when they are not measurable or integrable; deterministic policies give integrable totals for every fixed action sequence, and their finite maximum is integrable, so the source claim is preserved
--   - generalization: positive finite horizons in the theorem statements → all natural horizons, including T = 0; reason: the empty total reward, total penalty, inner value and Bellman value are all zero, so the conclusion extends to the terminal boundary
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, p. 11, Theorem 1, (20)–(22); proof §C.1, pp. 51–52, (84)–(100)

import Mathlib
import Definitions.Def_InfoRelaxTS_Monotone_Setting
import Definitions.Def_InfoRelaxTS_Monotone_Supplement_Duality

namespace InfoRelaxTS.Monotone.Supplement

open MeasureTheory ProbabilityTheory InfoRelaxTS.Monotone

/-- Theorem 1 (weak duality and strong duality), p. 11, (20)–(22), for the general Bayesian bandit
of §2.1 and every horizon `T` and prior `y`:
1. (weak duality, (20)) for every dual feasible penalty `z` the inner maximum is integrable (so
   `W^z(T, y)` is a genuine expectation), `W^z(T, y) ≥ V(π, T, y)` for every non-anticipating
   policy `π`, and `W^z(T, y) ≥ V*(T, y)`;
2. the ideal penalty `z^ideal` of (22) is dual feasible;
3. (strong duality, (21)) `W^ideal(T, y) = V*(T, y)`;
4. `V*(T, y)`, defined by the Bellman equations (15)–(16), is the least upper bound of
   `V(π, T, y)` over `π ∈ Π_𝔽` (17), so (20)–(21) hold for `V*` read as the optimal value. -/
theorem theorem_1 {K : ℕ} [NeZero K] {Θ Y : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    [Nonempty Θ] [MeasurableSpace Y]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : StandingAssumptions R P U)
    (T : ℕ) (y : Fin K → Y) :
    (∀ z : Penalty K Θ, DualFeasible R P z T y →
        Integrable (innerVal z T) (I R P y) ∧
          (∀ π : Policy K, V R P π T y ≤ W R P z T y) ∧ Vstar R P U T y ≤ W R P z T y) ∧
      DualFeasible R P (zIdeal R P U T y) T y ∧
      W R P (zIdeal R P U T y) T y = Vstar R P U T y ∧
      IsLUB (Set.range fun π : Policy K => V R P π T y) (Vstar R P U T y) := by sorry

end InfoRelaxTS.Monotone.Supplement
