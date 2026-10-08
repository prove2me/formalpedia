-- Prove2me | Theorems.Thm_MFGLiquidation_Equilibrium_riccati_mem_M
-- name    : MFGLiquidation.Equilibrium.riccati_mem_M
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:41.953831+00:00
-- url     : https://prove2.me/theorems/25dd1168-a05e-4832-b043-847ce9e39a82
-- title:
--   p. 9, after (2.8) — the singular Riccati solution A belongs to ℳ_{−1}
-- statement:
--   Under Assumption 2.3, let $(A,Z^A)$ solve the singular Riccati BSDE $-dA_t=(2\lambda_t-A_t^2/(2\eta_t))dt-Z^A_t\,d\widetilde W_t$, $A_T=\infty$, in $S^2_{\mathbb F}([0,T-])\times L^2_{\mathbb F}([0,T-];\mathbb R^m)$. Then $A\in\mathcal M_{-1}$, that is,
--   $$\operatorname*{ess\,sup}_{(t,\omega)\in[0,T]\times\Omega}(T-t)\,|A_t|<\infty .$$
--   This is the integrability class in which the paper uses $A$ throughout §2.1: it makes the singular driver $A_tB_t/(2\eta_t)$ of (2.10) comparable to $|B_t|/(T-t)$.
--
--   **Formalization Note** The paper attributes "$A\in\mathcal M_{-1}$" to Lemma A.1 (p. 9); here it is a separate statement about every solution in the class of Lemma A.1.
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, p. 9, after (2.8)

import Mathlib
import Definitions.Def_MFGLiquidation_Equilibrium_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLiquidation.Equilibrium

open Peng1990.SMP

theorem riccati_mem_M {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (D : Data Ω k) (hD : D.Standing P) (hA : D.Assumption23 P hD)
    (A : ℝ≥0 → Ω → ℝ) (ZA : Fin (k + 1) → ℝ≥0 → Ω → ℝ) (hR : IsSingularRiccati hD A ZA) :
    MemM (filtF hD) P D.T (-1) A := by sorry

end MFGLiquidation.Equilibrium
