-- Prove2me | Theorems.Thm_HedgePSNV_riskneutral_nv_maximizer_exists
-- name    : HedgePSNV.riskneutral_nv_maximizer_exists
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-08T00:14:44.232914+00:00
-- url     : https://prove2.me/theorems/e74f6969-b627-49f4-afd0-d7aa2ac514b7
-- title:
--   The risk-neutral newsvendor problem $\max_{(P,R)\in D}V_0(P,R)$ has a solution $(P^{NV(M)},R^{NV(M)})$
-- statement:
--   In the standing model of §3.1 (Brownian motions $B,\tilde B$, augmented filtrations, asset $X$, demand component $C$, market size $A_T=C_T+\tilde\sigma\tilde B_T$, risk-neutral measure $d\mathbb P^M/d\mathbb P=Z_T$), suppose $\mathbb E[((C_T)^-)^2]<\infty$, Assumption 5 holds ($Z$ is a square-integrable $\mathbb P$-martingale on $[0,T]$), and Assumption 1 holds for the law of $A_T$ under $\mathbb P^M$. Then the profit-maximization problem (2) with market size $A^M_T$ (the law of $A_T$ under $\mathbb P^M$) has a solution: there is $(P^{NV(M)},R^{NV(M)})\in D=\{P\ge c,\ R-bP\ge 0\}$ with
--
--   $$V_0(P,R)=\mathbb E^M[H_T(P,R)]\le V_0\big(P^{NV(M)},R^{NV(M)}\big)\qquad\text{for all }(P,R)\in D.$$
--
--   Role: the existence half of Proposition 1 for the risk-neutral market size; Theorem 2 combines Proposition 5 ($P^h_m\le P^{NV(M)}$, $R^h_m\le R^{NV(M)}$) with Proposition 4(i) ($P^{NV(M)}\le P^{NV}$, $R^{NV(M)}\le R^{NV}$), and both are statements about this maximizer, so it must exist.
--
--   **Formalization Note**: Proposition 1 is stated for the law of $A_T$; here it is applied to $A^M_T$, whose integrability ($\mathbb E^M[(A_T)^-]<\infty$) follows from $Z_T,(C_T)^-\in L^2(\mathbb P)$. Only existence is asserted; uniqueness and the optimality equations (4) are not.
-- source:
--   Wang, Yao, Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, https://arxiv.org/abs/2201.01026, Proposition 1, p.8 (problem (2) has a solution), applied to the market size A^M_T as in the definition of (P^{NV(M)}, R^{NV(M)}) before Proposition 4, pp.20-21

import Mathlib
import Definitions.Def_HedgePSNV_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNV

theorem riskneutral_nv_maximizer_exists (p : Params) {Ω : Type*} [MeasurableSpace Ω]
    (M : Model p Ω) (hM : M.Standing) (hL2 : M.NegPartL2) (h5 : M.Assumption5)
    (h1M : Assumption1 (M.PM.map M.AT)) :
    ∃ P R : ℝ, IsNVMaximizer p M.PM M.AT P R := by sorry

end HedgePSNV
