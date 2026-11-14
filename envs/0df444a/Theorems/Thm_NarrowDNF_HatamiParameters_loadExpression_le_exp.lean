-- Prove2me | Theorems.Thm_NarrowDNF_HatamiParameters_loadExpression_le_exp
-- name    : NarrowDNF.HatamiParameters.loadExpression_le_exp
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:13:58.327325+00:00
-- url     : https://prove2.me/theorems/45cff77c-f17e-47e2-9719-4e4d73fa45d6
-- title:
--   Exponential load bound for the exact threshold parameters
-- statement:
--   For real $e>0$ and $k\ge1$ satisfying $e^{-1}\le k$, set $\delta=2^{-100k^2}$ and $\eta=3^{-10k^2}e^{10k}$. The threshold-family load expression obeys
--   $$\frac{k2^{2k}}{\delta\eta^2}\le\exp(10000k^2).$$
--   This numerical lemma preserves both of the source parameter definitions and converts the multiplicity load estimate into a single exponential in the squared degree cutoff. At $k=1000C/a$ and $e=a/1000$, its exponent becomes $10^{10}C^2/a^2$.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiParameters.lean#L27-L53

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

theorem NarrowDNF.HatamiParameters.loadExpression_le_exp {e0 k : ℝ} (he0 : 0 < e0) (hk1 : 1 ≤ k)
    (hk : e0⁻¹ ≤ k) : loadExpression k e0 ≤ Real.exp (10000*k^2) := by sorry
