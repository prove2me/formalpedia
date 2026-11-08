-- Prove2me | Theorems.Thm_HedgePSNV_theorem_1_ii_upper_bound
-- name    : HedgePSNV.theorem_1_ii_upper_bound
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T14:36:29.955077+00:00
-- url     : https://prove2.me/theorems/48af3c42-fd02-4209-a355-2288222eb74e
-- title:
--   Upper bound in the minimal variance formula (21)
-- statement:
--   Under the hypotheses of Theorem 1(ii) and the martingale property of $X$ under $\mathbb P^M$, for all $m,P,R$, $$B(m,P,R)\le\frac{[m-V_0(P,R)]^2}{Z^M_0-1}+\int_0^T\mathbb E\Big[\frac{Z_t}{Z^M_t}\,\delta_t^2(P,R)\Big]dt.$$
--
--   Role: the inequality ' <= ' of formula (21).
-- source:
--   Wang-Yao-Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, https://arxiv.org/abs/2201.01026v4, Theorem 1(ii), (21), p. 15; proof of Theorem 1(ii), Section EC.7.3, pp. ec27-ec43

import Mathlib
import Definitions.Def_HedgePSNV_Hedging

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNV

theorem theorem_1_ii_upper_bound (p : Params) {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (hL2 : M.NegPartL2) (h4 : M.Assumption4) (h5 : M.Assumption5)
    (hne : ¬ (M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)))
    (hXM : IsMartingaleOn p.T M.F M.PM M.X) (m P R : ℝ) :
    M.Bval m P R ≤ ENNReal.ofReal ((m - M.V0 P R) ^ 2 / (M.ZM0 - 1)) +
        ∫⁻ u in Set.Icc (0 : ℝ) (p.T : ℝ), ∫⁻ ω,
          ENNReal.ofReal (M.Z u.toNNReal ω / M.ZM u.toNNReal ω * M.delta P R u.toNNReal ω ^ 2)
            ∂M.P := by sorry

end HedgePSNV
