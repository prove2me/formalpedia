-- Prove2me | Theorems.Thm_NarrowDNF_HatamiParameters_corrected_cross_bound
-- name    : NarrowDNF.HatamiParameters.corrected_cross_bound
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:13:56.064268+00:00
-- url     : https://prove2.me/theorems/88fbae93-87b7-484b-8c02-3cdfa3e74266
-- title:
--   Numerical control of the corrected cross expression
-- statement:
--   For real $e>0$ and $k\ge1$ with $e^{-1}\le k$, define the exact Appendix A parameters $\delta(k)=2^{-100k^2}$ and $\eta(k,e)=3^{-10k^2}e^{10k}$. Then
--   $$\frac{2^{9k}\delta(k)}{\eta(k,e)^2}\le e.$$
--   All powers with real exponents use real exponentiation on positive bases. This bound absorbs the corrected cross-term coefficient into the allotted error while keeping the paper's original parameter choices.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiParameters.lean#L76-L117

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_HatamiParameters

namespace NarrowDNF.HatamiParameters
end NarrowDNF.HatamiParameters
noncomputable section
open NarrowDNF
open NarrowDNF.HatamiParameters

theorem NarrowDNF.HatamiParameters.corrected_cross_bound {e0 k : ℝ} (he0 : 0 < e0) (hk1 : 1 ≤ k)
    (hk : e0⁻¹ ≤ k) : correctedCrossExpression k e0 ≤ e0 := by sorry
