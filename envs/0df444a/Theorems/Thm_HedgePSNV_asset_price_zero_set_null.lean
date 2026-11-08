-- Prove2me | Theorems.Thm_HedgePSNV_asset_price_zero_set_null
-- name    : HedgePSNV.asset_price_zero_set_null
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T14:46:37.156691+00:00
-- url     : https://prove2.me/theorems/836ea334-caeb-498c-8366-6e87da239cb9
-- title:
--   The asset price is almost surely non-zero at every positive time
-- statement:
--   Under Assumption 4, for $0<t\le T$, $$\mathbb P(X_t=0)=0.$$
--
--   Role: a step of the completeness argument (every square-integrable claim orthogonal to all hedgeable gains vanishes) (division by $X_t\sigma_t$).
-- source:
--   Wang-Yao-Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, https://arxiv.org/abs/2201.01026v4, Section 3.1, (2); proof of Theorem 1(ii), Section EC.7.3, pp. ec27-ec43

import Mathlib
import Definitions.Def_HedgePSNV_Hedging
import Definitions.Def_HedgePSNV_Model
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace HedgePSNV

theorem asset_price_zero_set_null {p : HedgePSNV.Params} {Ω : Type*} [MeasurableSpace Ω] (M : HedgePSNV.Model p Ω)
    (hM : M.Standing) (h4 : M.Assumption4) {t : ℝ≥0} (ht0 : 0 < t) (htT : t ≤ p.T) :
    M.P {ω | M.X t ω = 0} = 0 := by sorry

end HedgePSNV
