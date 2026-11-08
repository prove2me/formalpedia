-- Prove2me | Theorems.Thm_ImpulseGames_Verification_step1_deviation_bound_player_two
-- name    : ImpulseGames.Verification.step1_deviation_bound_player_two
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-07T08:06:00.834208+00:00
-- url     : https://prove2.me/theorems/d98aa048-be91-4a68-881a-24bc67646daf
-- title:
--   Theorem 3.3, proof, Step 1 (player 2, symmetric) — $V_2(x) \ge J^2(x;\varphi_1^*,\varphi_2)$ for every admissible deviation $\varphi_2$
-- statement:
--   Assume the hypotheses of Theorem 3.3 on $V_1,V_2,\delta_1,\delta_2$ — (3.1) with $\delta_i$ continuous on $S$, the QVI system (3.3), (ii) and (iii) — and let $x\in S$. Let $\varphi_1^*=(\mathcal D_1,\delta_1)$. Then for every strategy $\varphi_2=(\mathcal C_2,\xi_2)$ of player 2 such that $(\varphi_1^*,\varphi_2)\in\Phi_x$,
--   $$
--   V_2(x)\ \ge\ J^2(x;\varphi_1^*,\varphi_2),
--   $$
--   the payoff being computed on any admissible realization.
--
--   This is the second Nash inequality of Theorem 3.3. The paper proves Step 1 for player 1 and states that "the arguments for $V_2$ and $J^2$ [are] symmetric"; this is that symmetric statement, the counterpart of `ImpulseGames.Verification.step1_deviation_bound`.
--
--   **Formalization Note.** As in the player-1 milestone, the admissibility of $(\varphi_1^*,\varphi_2^*)$ is not used by this step and is omitted. The model gives player 1 priority at simultaneous exits, so the statement is not a formal relabelling of the player-1 one and is stated separately.
-- source:
--   Aïd et al. (2020), Math. Oper. Res. 45(1), accepted manuscript (arXiv:1605.00039v4), proof of Theorem 3.3, Step 1 (pp. 10–11) and the sentence 'the arguments for V2 and J2 being symmetric' (p. 10)

import Mathlib
import Definitions.Def_ImpulseGames_Verification_Game
import Definitions.Def_ImpulseGames_Verification_QVI

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ImpulseGames.Verification

/-- Step 1 of the proof of Theorem 3.3, player 2 (the symmetric case): under the hypotheses of
Theorem 3.3 (except the admissibility of `(φ_1^*, φ_2^*)`), for every strategy `φ_2 = (C2, ξ2)`
of player 2 with `(φ_1^*, φ_2) ∈ Φ_x`, `V_2(x) ≥ J^2(x; φ_1^*, φ_2)`. -/
theorem step1_deviation_bound_player_two {d k : ℕ} {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m) (W : ℝ≥0 → Ω → (Fin k → ℝ))
    (hW : IsBrownianBasis P 𝔽 W) (G : Game d k) (hG : G.Standing)
    (V : Player → State d → ℝ) (δ : (i : Player) → State d → G.Imp i)
    (hV : VerificationHypotheses G V δ) (x : State d) (hx : x ∈ G.S)
    (C2 : Set (State d)) (ξ2 : State d → G.Imp .two) (Y : ℕ → ℝ≥0 → Ω → State d)
    (hY : IsAdmissible P 𝔽 W G x ((starProfile G V δ).update .two C2 ξ2) Y) :
    payoff P G x ((starProfile G V δ).update .two C2 ξ2) Y .two ≤ V .two x := by sorry

end ImpulseGames.Verification
