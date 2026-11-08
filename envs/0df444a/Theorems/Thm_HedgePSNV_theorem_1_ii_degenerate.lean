-- Prove2me | Theorems.Thm_HedgePSNV_theorem_1_ii_degenerate
-- name    : HedgePSNV.theorem_1_ii_degenerate
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T21:18:58.339206+00:00
-- url     : https://prove2.me/theorems/564778c0-ff7b-40e6-b7de-0977dc7fe05a
-- title:
--   Theorem 1(ii) when $\mathbb P^M=\mathbb P$: $B(m,P,R)$ is the unhedgeable risk if $V_0(P,R)=m$ and $+\infty$ otherwise
-- statement:
--   In the standing model of §3.1 (Brownian motions $B,\tilde B$, augmented filtrations $\mathcal F_t\supseteq\mathcal G_t$, asset $X$, demand component $C$, market size $A_T=C_T+\tilde\sigma\tilde B_T$, density process $Z$, risk-neutral measure $d\mathbb P^M/d\mathbb P=Z_T$, $Z^M_t=\mathbb E^M(Z_T\mid\mathcal F_t)$, $\delta_t(P,R)=\tilde\sigma(P-s)\mathbb P^M(A_T\le R\mid\mathcal F_t)$ of (19)), suppose Assumptions 4–5 hold, $\mathbb E[((C_T)^-)^2]<\infty$, and $Z_T=1$ almost surely (so $\mathbb P^M=\mathbb P$ and $Z^M_0=1$). Then the optimal value of the hedging problem (14) is
--
--   $$B(m,P,R)=\begin{cases}\displaystyle\int_0^T\mathbb E\Big[\frac{Z_t}{Z^M_t}\,\delta_t^2(P,R)\Big]\,dt, & V_0(P,R)=m,\\ +\infty, & V_0(P,R)\ne m,\end{cases}$$
--
--   i.e. formula (21) with its first term $[m-V_0(P,R)]^2/(Z^M_0-1)$ read as $0$ or $+\infty$ at $Z^M_0=1$.
--
--   Role: the formal Theorem 1(ii) excludes $\mathbb P^M=\mathbb P$ (its first term divides by $Z^M_0-1$); Proposition 5 and Lemma EC.7 are stated without that exclusion, so their proofs need the structure of $B$ in this case as well.
--
--   **Formalization Note**: $B$ is the infimum in $[0,\infty]$ of the extended variance (Bval), so an empty feasible set gives $+\infty$; the right side is written with the same lower Lebesgue integral as the formal Theorem 1(ii).
-- source:
--   Wang, Yao, Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, https://arxiv.org/abs/2201.01026, Theorem 1(ii), formula (21), p.15, in the case P^M = P (Z^M_0 = E(Z_T^2) = 1), with the decomposition (18) and delta_t of (19), p.15

import Mathlib
import Definitions.Def_HedgePSNV_Hedging

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNV

theorem theorem_1_ii_degenerate (p : Params) {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (hL2 : M.NegPartL2) (h4 : M.Assumption4) (h5 : M.Assumption5)
    (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)) :
    ∀ m P R : ℝ, M.Bval m P R =
      (if M.V0 P R = m then 0 else ⊤) +
        ∫⁻ u in Set.Icc (0 : ℝ) (p.T : ℝ), ∫⁻ ω,
          ENNReal.ofReal (M.Z u.toNNReal ω / M.ZM u.toNNReal ω * M.delta P R u.toNNReal ω ^ 2)
            ∂M.P := by sorry

end HedgePSNV
