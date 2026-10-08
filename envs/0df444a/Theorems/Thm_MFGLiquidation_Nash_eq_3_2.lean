-- Prove2me | Theorems.Thm_MFGLiquidation_Nash_eq_3_2
-- name    : MFGLiquidation.Nash.eq_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:26.369392+00:00
-- url     : https://prove2.me/theorems/8c4df75c-cf49-4ad9-8804-1cba7054b86f
-- title:
--   (3.2) — all players' equilibrium rates have the same conditional mean µ* given 𝔽⁰
-- statement:
--   In the setting of Lemma 3.2 (Assumption 3.1, the standing Assumption 2.3 for every player, and for every player $i$ a solution $(X^i,Y^i,Z^i)$ of (2.3) in the class of Theorem 2.4), there is a single $\mathbb F^0$-progressive process $\mu^*$ such that for every player $i$
--   $$\mu^*_t=\mathbb E\big[\xi^{*,i}_t\,\big|\,\mathcal F^0_t\big]\qquad\text{a.s., for a.e. }t\in[0,T], \tag{3.2}$$
--   where $\xi^{*,i}=Y^i/(2\eta^i)$ and $\mathbb F^0$ is the (augmented) filtration of the common noise $W^0$.
--
--   Each player's FBSDE involves its own conditional mean $\mathbb E[\xi^{*,i}_t\mid\mathcal F^0_t]$; (3.2) says these coincide, so all players face the same mean-field equilibrium $\mu^*$.
--
--   **Formalization Note.** Players are indexed from $0$. Assumption 2.3 per player is the paper's standing assumption. "a.s. a.e." is read as: $\xi^{*,i}_t$ is integrable and $\mu^*_t=\mathbb E[\xi^{*,i}_t\mid\mathcal F^0_t]$ a.s., for Lebesgue-a.e. $t\in[0,T]$, with $\mu^*$ progressive for $\mathbb F^0$.
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, p. 22, (3.2)

import Mathlib
import Definitions.Def_MFGLiquidation_Nash_Setting
import Definitions.Def_MFGLiquidation_Nash_Game
import Definitions.Def_MFGLiquidation_Nash_Players

open MeasureTheory ProbabilityTheory Filter Topology Peng1990.SMP
open scoped ENNReal NNReal

namespace MFGLiquidation.Nash

theorem eq_3_2
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (Pop : Population Ω k) (ν : Measure ℝ) (hstd : Pop.Standing P ν)
    (h31 : Pop.Assumption31)
    (h23 : ∀ i, (Pop.player i).Assumption23 P (hstd.player i))
    (Xp Yp : ℕ → ℝ≥0 → Ω → ℝ) (Zp : ℕ → Fin (k + 1) → ℝ≥0 → Ω → ℝ)
    (hsol : ∀ i, SolvesFBSDE23InClass (hstd.player i) (Xp i) (Yp i) (Zp i)) :
    ∃ μ : ℝ≥0 → Ω → ℝ, ∀ i,
      IsCondExpVersion (filtF0 (hstd.player i)) P Pop.T (Pop.xiStar Yp i) μ := by sorry

end MFGLiquidation.Nash
