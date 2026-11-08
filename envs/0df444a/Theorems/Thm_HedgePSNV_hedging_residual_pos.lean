-- Prove2me | Theorems.Thm_HedgePSNV_hedging_residual_pos
-- name    : HedgePSNV.hedging_residual_pos
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T23:04:51.313206+00:00
-- url     : https://prove2.me/theorems/79f89ebd-f97b-435a-95a2-01a4339d7839
-- title:
--   The unhedgeable risk $\int_0^T\mathbb E[(Z_t/Z^M_t)\,\delta_t^2(P,R)]\,dt$ is strictly positive for $P>s$
-- statement:
--   In the standing model of §3.1 (Brownian motions $B,\tilde B$, augmented filtrations $\mathcal F_t\supseteq\mathcal G_t$, asset $X$, demand component $C$, market size $A_T=C_T+\tilde\sigma\tilde B_T$, density process $Z$, risk-neutral measure $d\mathbb P^M/d\mathbb P=Z_T$, $Z^M_t=\mathbb E^M(Z_T\mid\mathcal F_t)$, $\delta_t(P,R)=\tilde\sigma(P-s)\mathbb P^M(A_T\le R\mid\mathcal F_t)$ of (19)), suppose Assumption 5 holds ($Z$ is a square-integrable $\mathbb P$-martingale on $[0,T]$) and Assumption 1 holds for the law of $A_T$ under $\mathbb P^M$. Then for every $P>s$ and every $R$ the second term of $B(m,P,R)$ in (21) is strictly positive:
--
--   $$\Psi(P,R):=\int_0^T\mathbb E\Big[\frac{Z_t}{Z^M_t}\,\delta_t^2(P,R)\Big]\,dt>0 .$$
--
--   Role: in the proof of Proposition 5 (EC.8.2) the unhedgeable risk $\Psi$ is strictly increasing in $P$; since $\Psi(P,R)$ scales exactly by $((P-s)/(P_1-s))^2$ in $P$, strict increase is equivalent to this positivity, which rules out a minimizer of $B$ that dominates a comparison point.
--
--   **Formalization Note**: the time integral is the lower Lebesgue integral over $[0,T]$ of the (nonnegative) expectation, exactly as in the formal Theorem 1(ii).
-- source:
--   Wang, Yao, Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, https://arxiv.org/abs/2201.01026, EC.8.2, proof of Proposition 7, p.ec48 ("Psi(P,R) strictly increases in both P and R"), with delta_t of (19) and the second term of (21), p.15

import Mathlib
import Definitions.Def_HedgePSNV_Hedging

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNV

theorem hedging_residual_pos (p : Params) {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h5 : M.Assumption5) (h1M : Assumption1 (M.PM.map M.AT))
    (P R : ℝ) (hP : p.s < P) :
    0 < ∫⁻ u in Set.Icc (0 : ℝ) (p.T : ℝ), ∫⁻ ω,
        ENNReal.ofReal (M.Z u.toNNReal ω / M.ZM u.toNNReal ω * M.delta P R u.toNNReal ω ^ 2)
          ∂M.P := by sorry

end HedgePSNV
