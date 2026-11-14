-- Prove2me | Theorems.Thm_NarrowDNF_BourgainParameters_first_term_le
-- name    : NarrowDNF.BourgainParameters.first_term_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:10:49.963382+00:00
-- url     : https://prove2.me/theorems/c7ca071d-eb12-4891-a80d-1b9ec944025c
-- title:
--   The rounded Bourgain cutoff preserves the first error bound
-- statement:
--   Let \(k\ge1\) be an integer and \(0<e\le1\). Define the real cutoff, its integer rounding, and the component threshold by
--   $$R=\frac{3^{18k}}{e^{10}},\qquad M=\lceil R\rceil,\qquad \eta=\frac{e^{10k}}{3^{10k^2}}.$$
--   Then
--   $$M^k\eta^2\le\frac{e^2}{3^k}.$$
--   Thus the counting contribution in the Bourgain error budget remains small when its cutoff is replaced by an actual integer. The ceiling here is the nonnegative integer ceiling, which agrees with the usual ceiling because \(R\ge1\).
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainParameters.lean#L56-L91

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_BourgainParameters

namespace NarrowDNF.BourgainParameters
end NarrowDNF.BourgainParameters
noncomputable section
open NarrowDNF
open NarrowDNF.BourgainParameters

theorem NarrowDNF.BourgainParameters.first_term_le {k : ℕ} (hk : 1 ≤ k) {e : ℝ}
    (he0 : 0 < e) (he1 : e ≤ 1) :
    (cutoff k e : ℝ)^k * (eta k e)^2 ≤ e^2 / (3:ℝ)^k := by sorry
