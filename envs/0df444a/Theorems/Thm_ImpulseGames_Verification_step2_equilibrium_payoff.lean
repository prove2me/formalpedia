-- Prove2me | Theorems.Thm_ImpulseGames_Verification_step2_equilibrium_payoff
-- name    : ImpulseGames.Verification.step2_equilibrium_payoff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:26:17.335697+00:00
-- url     : https://prove2.me/theorems/2e4351db-823e-4f56-afb4-d9e5f74979c9
-- title:
--   Theorem 3.3, proof, Step 2 — $V_1(x)=J^1(x;\varphi_1^*,\varphi_2^*)$
-- statement:
--   Assume the hypotheses of Theorem 3.3 on $V_1,V_2,\delta_1,\delta_2$ — (3.1) with $\delta_i$ continuous on $S$, the QVI system (3.3), (ii) and (iii), and let $x\in S$. Let $\varphi_i^*=(\mathcal D_i,\delta_i)$. If $(\varphi_1^*,\varphi_2^*)\in\Phi_x$, then
--   $$
--   V_1(x)=J^1(x;\varphi_1^*,\varphi_2^*),
--   $$
--   the payoff being computed on any admissible realization.
--
--   The inequalities of Step 1 become equalities when player 1 plays $\varphi_1^*$; this identifies $V_1(x)$ as player 1's equilibrium payoff.
--
--   **Formalization Note.** The admissibility of $(\varphi_1^*,\varphi_2^*)$ is expressed by the admissible realization on which the payoff is computed.
-- source:
--   Aïd et al. (2020), Math. Oper. Res. 45(1), accepted manuscript, proof of Theorem 3.3, Step 2 (p. 12)

import Mathlib
import Definitions.Def_ImpulseGames_Verification_Game
import Definitions.Def_ImpulseGames_Verification_QVI

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ImpulseGames.Verification

/-- Step 2 of the proof of Theorem 3.3: under the hypotheses of Theorem 3.3, for every
admissible realization `Y` of `(φ_1^*, φ_2^*)` (so `(φ_1^*, φ_2^*) ∈ Φ_x`),
`V_1(x) = J^1(x; φ_1^*, φ_2^*)`. -/
theorem step2_equilibrium_payoff {d k : ℕ} {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m) (W : ℝ≥0 → Ω → (Fin k → ℝ))
    (hW : IsBrownianBasis P 𝔽 W) (G : Game d k) (hG : G.Standing)
    (V : Player → State d → ℝ) (δ : (i : Player) → State d → G.Imp i)
    (hV : VerificationHypotheses G V δ) (x : State d) (hx : x ∈ G.S)
    (Y : ℕ → ℝ≥0 → Ω → State d) (hY : IsAdmissible P 𝔽 W G x (starProfile G V δ) Y) :
    V .one x = payoff P G x (starProfile G V δ) Y .one := by sorry

end ImpulseGames.Verification
