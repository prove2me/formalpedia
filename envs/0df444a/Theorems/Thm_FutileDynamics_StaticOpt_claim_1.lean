-- Prove2me | Theorems.Thm_FutileDynamics_StaticOpt_claim_1
-- name    : FutileDynamics.StaticOpt.claim_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:50:34.632243+00:00
-- url     : https://prove2.me/theorems/03608f41-8ca5-43af-b7dd-d53ac3e49541
-- title:
--   Claim 1, p. ec 9 — round t of a deviation σ′ against S×T is replicated by a single-round strategy against S with expected utilities Vt, Ut
-- statement:
--   Let $S$ be a single-round direct mechanism with rule $\tilde\pi$, and $S^{\times T}$ its $T$-fold repetition. Let $F'$ be a distribution and $\sigma'$ a feasible agent strategy against $S^{\times T}$. For a round $t\in\{1,\dots,T\}$ let
--   $$V_t=\mathbb E[v(\theta_t,\omega_t)],\qquad U_t=\mathbb E[u(\theta_t,\omega_t)]$$
--   be the expected round-$t$ utilities when the agent plays $\sigma'$ against $S^{\times T}$ under $F'$. Here $\omega_t=\tilde\pi(\sigma'_t(\theta_t,h^+_t),z_t)$ if the agent participated and $\omega_t=\emptyset$ after QUIT. Then there is a feasible agent strategy against $S$, at horizon 1 and under $F'$, whose expected agent utility is $V_t$ and whose expected principal utility is $U_t$.
--
--   The claim is the step of Lemma 5 showing that $S^{\times T}$ inherits incentive compatibility from $S$.
--
--   **Formalization Note** Proved for every direct rule; IC of $S$ is not needed. Round $t$ is `k : Fin T` with $t=k+1$. $\Theta$ standard Borel lets the agent simulate the past shocks from its private uniform. Also assumed: $0<T$, nonempty $\Theta$, and the model conventions.
-- source:
--   Balseiro, Kim & Russo, On the futility of dynamics in robust mechanism design, SSRN 3449698 (version of October 5, 2020), p. ec 9, Claim 1 (in the proof of Lemma 5) and the definition of Vt, Ut

import Mathlib
import Definitions.Def_FutileDynamics_StaticOpt_Model

namespace FutileDynamics.StaticOpt

open MeasureTheory

/-- **Claim 1** (p. ec 9): let `S^{×T}` repeat the direct rule `d`, let `F'` be a distribution and `σ'` a
feasible agent strategy against `S^{×T}`. For any round `t = k + 1` there is a feasible agent strategy against
the single-round mechanism `S` whose expected agent and principal utilities equal the round-`t` expected
utilities `V_t = E[v(θ_t, ω_t)]` and `U_t = E[u(θ_t, ω_t)]` of `σ'` against `S^{×T}`. -/
theorem claim_1 {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ] [Nonempty Θ]
    (G : Game Θ Ω) (T : ℕ) (hT : 0 < T) (d : DirectRule G) (F' : Measure Θ)
    (hF' : IsProbabilityMeasure F')
    (σ' : Strategy Θ Ω (repeatDirect G d).M0 (repeatDirect G d).M) (hσ' : σ'.Feasible) (k : Fin T) :
    ∃ σ'' : Strategy Θ Ω (repeatDirect G d).M0 (repeatDirect G d).M, σ''.Feasible ∧
      agentUtility G (repeatDirect G d) σ'' F' 1 = roundAgentUtility G (repeatDirect G d) σ' F' T k ∧
      principalUtility G (repeatDirect G d) σ'' F' 1 =
        roundPrincipalUtility G (repeatDirect G d) σ' F' T k := by sorry

end FutileDynamics.StaticOpt
