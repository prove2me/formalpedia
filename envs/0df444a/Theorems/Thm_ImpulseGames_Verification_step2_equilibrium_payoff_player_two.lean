-- Prove2me | Theorems.Thm_ImpulseGames_Verification_step2_equilibrium_payoff_player_two
-- name    : ImpulseGames.Verification.step2_equilibrium_payoff_player_two
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-07T08:06:01.246054+00:00
-- url     : https://prove2.me/theorems/b3814ad9-f2f6-4384-9e9f-1ba5cbbd7489
-- title:
--   Theorem 3.3, proof, Step 2 (player 2, symmetric) — $V_2(x) = J^2(x;\varphi_1^*,\varphi_2^*)$
-- statement:
--   Assume the hypotheses of Theorem 3.3 on $V_1,V_2,\delta_1,\delta_2$ — (3.1) with $\delta_i$ continuous on $S$, the QVI system (3.3), (ii) and (iii) — and let $x\in S$. Then for every admissible realization of the candidate equilibrium $(\varphi_1^*,\varphi_2^*)$, $\varphi_i^*=(\mathcal D_i,\delta_i)$,
--   $$
--   V_2(x)\ =\ J^2(x;\varphi_1^*,\varphi_2^*).
--   $$
--
--   The paper proves Step 2 for player 1 ("we argue as in Step 1, but here all the inequalities are equalities by the properties of $\varphi_1^*$") and states that the arguments for player 2 are symmetric; this is that symmetric statement, the counterpart of `ImpulseGames.Verification.step2_equilibrium_payoff`.
--
--   **Formalization Note.** The model gives player 1 priority at simultaneous exits, so the statement is not a formal relabelling of the player-1 one and is stated separately.
-- source:
--   Aïd et al. (2020), Math. Oper. Res. 45(1), accepted manuscript (arXiv:1605.00039v4), proof of Theorem 3.3, Step 2 (p. 12) and the sentence 'the arguments for V2 and J2 being symmetric' (p. 10)

import Mathlib
import Definitions.Def_ImpulseGames_Verification_Game
import Definitions.Def_ImpulseGames_Verification_QVI

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ImpulseGames.Verification

/-- Step 2 of the proof of Theorem 3.3, player 2 (the symmetric case): under the hypotheses of
Theorem 3.3, for every admissible realization `Y` of `(φ_1^*, φ_2^*)`,
`V_2(x) = J^2(x; φ_1^*, φ_2^*)`. -/
theorem step2_equilibrium_payoff_player_two {d k : ℕ} {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m) (W : ℝ≥0 → Ω → (Fin k → ℝ))
    (hW : IsBrownianBasis P 𝔽 W) (G : Game d k) (hG : G.Standing)
    (V : Player → State d → ℝ) (δ : (i : Player) → State d → G.Imp i)
    (hV : VerificationHypotheses G V δ) (x : State d) (hx : x ∈ G.S)
    (Y : ℕ → ℝ≥0 → Ω → State d) (hY : IsAdmissible P 𝔽 W G x (starProfile G V δ) Y) :
    V .two x = payoff P G x (starProfile G V δ) Y .two := by sorry

end ImpulseGames.Verification
