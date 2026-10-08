-- Prove2me | Theorems.Thm_MFGLiquidation_Nash_eq_3_3
-- name    : MFGLiquidation.Nash.eq_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:08.371974+00:00
-- url     : https://prove2.me/theorems/97e51c82-9259-4eaa-9150-61e22c8c381e
-- title:
--   (3.3) — a uniform bound E∫₀ᵀ|ξ^{*,i}_t|² dt ≤ C for all players
-- statement:
--   In the setting of Lemma 3.2, there is a constant $C$, the same for every player $i$, such that
--   $$\mathbb E\Big[\int_0^T|\xi^{*,i}_t|^2\,dt\Big]\le C, \tag{3.3}$$
--   where $\xi^{*,i}=Y^i/(2\eta^i)$ is player $i$'s mean-field strategy.
--
--   The paper attributes this bound to Proposition 2.8; it is one of the two moment bounds that feed the estimate (3.5).
--
--   **Formalization Note.** The constant is quantified before the player index, so it is uniform over all players; a bound for each player separately would be mere finiteness. The expectation is computed in $[0,\infty]$. Assumption 2.3 per player is the paper's standing assumption.
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, p. 22, (3.3)

import Mathlib
import Definitions.Def_MFGLiquidation_Nash_Setting
import Definitions.Def_MFGLiquidation_Nash_Game
import Definitions.Def_MFGLiquidation_Nash_Players

open MeasureTheory ProbabilityTheory Filter Topology Peng1990.SMP
open scoped ENNReal NNReal

namespace MFGLiquidation.Nash

theorem eq_3_3
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (Pop : Population Ω k) (ν : Measure ℝ) (hstd : Pop.Standing P ν)
    (h31 : Pop.Assumption31)
    (h23 : ∀ i, (Pop.player i).Assumption23 P (hstd.player i))
    (Xp Yp : ℕ → ℝ≥0 → Ω → ℝ) (Zp : ℕ → Fin (k + 1) → ℝ≥0 → Ω → ℝ)
    (hsol : ∀ i, SolvesFBSDE23InClass (hstd.player i) (Xp i) (Yp i) (Zp i)) :
    ∃ C : ℝ, ∀ i,
      ∫⁻ ω, ∫⁻ t in Set.Icc (0 : ℝ) Pop.T, ‖Pop.xiStar Yp i t.toNNReal ω‖ₑ ^ 2 ∂volume ∂P
        ≤ ENNReal.ofReal C := by sorry

end MFGLiquidation.Nash
