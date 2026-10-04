-- Prove2me | Theorems.Thm_ImpulseGames_Verification_step1_deviation_bound
-- name    : ImpulseGames.Verification.step1_deviation_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:26:10.22211+00:00
-- url     : https://prove2.me/theorems/efa5f7aa-cd7f-4c6a-a3c1-0e6ff3c3c186
-- title:
--   Theorem 3.3, proof, Step 1 — $V_1(x)\ge J^1(x;\varphi_1,\varphi_2^*)$ for every admissible deviation $\varphi_1$
-- statement:
--   Assume the hypotheses of Theorem 3.3 on $V_1,V_2,\delta_1,\delta_2$ — (3.1) with $\delta_i$ continuous on $S$, the QVI system (3.3), (ii) and (iii), and let $x\in S$. Let $\varphi_2^*=(\mathcal D_2,\delta_2)$. Then for every strategy $\varphi_1$ of player 1 such that $(\varphi_1,\varphi_2^*)\in\Phi_x$,
--   $$
--   V_1(x)\ \ge\ J^1(x;\varphi_1,\varphi_2^*),
--   $$
--   the payoff being computed on any admissible realization.
--
--   This is the first of the two Nash inequalities; together with Step 2 and the symmetric statements for player 2 it proves Theorem 3.3.
--
--   **Formalization Note.** The admissibility of $(\varphi_1^*,\varphi_2^*)$, a hypothesis of Theorem 3.3, is not used by this step and is omitted.
-- source:
--   Aïd et al. (2020), Math. Oper. Res. 45(1), accepted manuscript, proof of Theorem 3.3, Step 1 (pp. 10–11)

import Mathlib
import Definitions.Def_ImpulseGames_Verification_Game
import Definitions.Def_ImpulseGames_Verification_QVI

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ImpulseGames.Verification

/-- Step 1 of the proof of Theorem 3.3: under the hypotheses of Theorem 3.3 (except the
admissibility of `(φ_1^*, φ_2^*)`, which this step does not use), for every strategy
`φ_1 = (C1, ξ1)` of player 1 with `(φ_1, φ_2^*) ∈ Φ_x`, `V_1(x) ≥ J^1(x; φ_1, φ_2^*)`. -/
theorem step1_deviation_bound {d k : ℕ} {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m) (W : ℝ≥0 → Ω → (Fin k → ℝ))
    (hW : IsBrownianBasis P 𝔽 W) (G : Game d k) (hG : G.Standing)
    (V : Player → State d → ℝ) (δ : (i : Player) → State d → G.Imp i)
    (hV : VerificationHypotheses G V δ) (x : State d) (hx : x ∈ G.S)
    (C1 : Set (State d)) (ξ1 : State d → G.Imp .one) (Y : ℕ → ℝ≥0 → Ω → State d)
    (hY : IsAdmissible P 𝔽 W G x ((starProfile G V δ).update .one C1 ξ1) Y) :
    payoff P G x ((starProfile G V δ).update .one C1 ξ1) Y .one ≤ V .one x := by sorry

end ImpulseGames.Verification
