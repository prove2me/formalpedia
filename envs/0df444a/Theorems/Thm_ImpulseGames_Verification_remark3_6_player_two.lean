-- Prove2me | Theorems.Thm_ImpulseGames_Verification_remark3_6_player_two
-- name    : ImpulseGames.Verification.remark3_6_player_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:25:51.759665+00:00
-- url     : https://prove2.me/theorems/1282e3d7-6b49-42bf-b534-31fe253a2f8f
-- title:
--   Remark 3.6, (3.8b), (3.8d), (3.8f) — against $\varphi_2^*$ the state stays in $\mathcal D_2$ and player 2 acts on $\{\mathcal M_2V_2=V_2\}$ with impulse $\delta_2$
-- statement:
--   Assume the hypotheses of Theorem 3.3 on $V_1,V_2,\delta_1,\delta_2$: (3.1) with $\delta_i$ continuous on $S$, the QVI system (3.3), and the regularity conditions (ii)–(iii). Let $x\in S$, let $\varphi_1=(\mathcal C_1,\xi_1)$ be a strategy of player 1 such that $(\varphi_1,\varphi_2^*)\in\Phi_x$, where $\varphi_2^*=(\mathcal D_2,\delta_2)$, and let $X,\tau_S,\tau_{2,n},\delta_{2,n}$ be the corresponding controlled process, exit time and controls of player 2 on an admissible realization. Then, for every $\omega$:
--
--   1. for every $s\in\,]0,\tau_S[$ that is not an intervention time,
--   $$(\mathcal M_2V_2-V_2)(X_s)<0 ;\tag{3.8b}$$
--   2. for every $n\ge1$ with $\tau_{2,n}<\tau_S$,
--   $$\delta_{2,n}=\delta_2\big(X_{(\tau_{2,n})^-}\big),\tag{3.8d}$$
--   $$(\mathcal M_2V_2-V_2)\big(X_{(\tau_{2,n})^-}\big)=0.\tag{3.8f}$$
--
--   These identities are what Step 1 of the proof of Theorem 3.3 uses: player 1's payoff can be compared with $V_1$ only because, against $\varphi_2^*$, the state never leaves $\mathcal D_2$ and player 2 intervenes only on $\{\mathcal M_2V_2=V_2\}$ with her optimal impulse.
--
--   **Formalization Note.** The page states (3.8b) for "every $s\ge0$" and (3.8d), (3.8f) for every $\tau_{2,k}<\infty$. $\mathcal M_2V_2$ is defined only on $S$ and the controls are only meaningful before the end of the game, so the statement uses $s\in\,]0,\tau_S[$ off the intervention times and $\tau_{2,n}<\tau_S$; Lemma 2.3 explains why $s=0$ and intervention instants must be excluded. The symmetric statements (3.8a), (3.8c), (3.8e) for player 1 are not stated separately.
-- source:
--   Aïd et al. (2020), Math. Oper. Res. 45(1), accepted manuscript, Remark 3.6, (3.8b), (3.8d), (3.8f) (p. 10)

import Mathlib
import Definitions.Def_ImpulseGames_Verification_Game
import Definitions.Def_ImpulseGames_Verification_QVI

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ImpulseGames.Verification

/-- Remark 3.6, (3.8b), (3.8d), (3.8f): under the hypotheses of Theorem 3.3, for every strategy
`φ_1 = (C1, ξ1)` with `(φ_1, φ_2^*) ∈ Φ_x` and every sample path of an admissible realization,
`(𝓜_2 V_2 - V_2)(X_s) < 0` at every `s ∈ ]0, τ_S[` that is not an intervention time, and at every
intervention of player 2 before `τ_S`, `δ_{2,n} = δ_2(X_{(τ_{2,n})^-})` and
`(𝓜_2 V_2 - V_2)(X_{(τ_{2,n})^-}) = 0`. -/
theorem remark3_6_player_two {d k : ℕ} {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m) (W : ℝ≥0 → Ω → (Fin k → ℝ))
    (hW : IsBrownianBasis P 𝔽 W) (G : Game d k) (hG : G.Standing)
    (V : Player → State d → ℝ) (δ : (i : Player) → State d → G.Imp i)
    (hV : VerificationHypotheses G V δ) (x : State d) (hx : x ∈ G.S)
    (C1 : Set (State d)) (ξ1 : State d → G.Imp .one) (Y : ℕ → ℝ≥0 → Ω → State d)
    (hY : IsAdmissible P 𝔽 W G x ((starProfile G V δ).update .one C1 ξ1) Y) (ω : Ω) :
    (∀ s : ℝ≥0, 0 < s →
      (s : ℝ≥0∞) < exitTime G x ((starProfile G V δ).update .one C1 ξ1) (pathOf Y ω) →
      (s : ℝ≥0∞) ∉ interventionTimes G x ((starProfile G V δ).update .one C1 ξ1) (pathOf Y ω) →
      interventionOp G V δ .two
          (ctrl G x ((starProfile G V δ).update .one C1 ξ1) (pathOf Y ω) s)
        - V .two (ctrl G x ((starProfile G V δ).update .one C1 ξ1) (pathOf Y ω) s) < 0) ∧
    (∀ n : ℕ, 1 ≤ n →
      interTime G x ((starProfile G V δ).update .one C1 ξ1) (pathOf Y ω) .two n <
        exitTime G x ((starProfile G V δ).update .one C1 ξ1) (pathOf Y ω) →
      impulse G x ((starProfile G V δ).update .one C1 ξ1) (pathOf Y ω) .two n =
          δ .two (preState G x ((starProfile G V δ).update .one C1 ξ1) (pathOf Y ω) .two n) ∧
        interventionOp G V δ .two
            (preState G x ((starProfile G V δ).update .one C1 ξ1) (pathOf Y ω) .two n)
          - V .two (preState G x ((starProfile G V δ).update .one C1 ξ1) (pathOf Y ω) .two n)
          = 0) := by sorry

end ImpulseGames.Verification
