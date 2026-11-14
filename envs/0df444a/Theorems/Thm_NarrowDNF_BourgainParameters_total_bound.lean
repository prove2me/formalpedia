-- Prove2me | Theorems.Thm_NarrowDNF_BourgainParameters_total_bound
-- name    : NarrowDNF.BourgainParameters.total_bound
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:18:50.828371+00:00
-- url     : https://prove2.me/theorems/013c4dd7-fa6d-4ef5-9ba8-1d1454fc7adf
-- title:
--   An explicit three-term Bourgain error budget
-- statement:
--   Let \(k\ge5\) be an integer, \(0<e\le1\), and \(0\le C\le k\). Set
--   $$M=\left\lceil\frac{3^{18k}}{e^{10}}\right\rceil,\quad \eta=\frac{e^{10k}}{3^{10k^2}},\quad \tau=\frac{e^3}{3^{6k}}.$$
--   The three contributions in the reconstructed small-component estimate satisfy
--   $$M^k\eta^2+2C3^{2k}\tau^{2/3}+\frac{3^{2k}\sqrt C}{\sqrt M\,\tau}\le\frac{e^2}{2k}.$$
--   This supplies a numerical error budget with an integer cutoff and the original component threshold, uniformly over every admissible \(C\). Each quantity has exactly the explicit parameter dependence displayed above.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainParameters.lean#L147-L168

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_BourgainParameters
import Theorems.Thm_NarrowDNF_BourgainParameters_first_term_le

namespace NarrowDNF.BourgainParameters
end NarrowDNF.BourgainParameters
noncomputable section
open NarrowDNF
open NarrowDNF.BourgainParameters

theorem NarrowDNF.BourgainParameters.total_bound {k : ℕ} (hk : 5 ≤ k) {e C : ℝ}
    (he0 : 0 < e) (he1 : e ≤ 1) (hC0 : 0 ≤ C) (hC : C ≤ k) :
    (cutoff k e : ℝ)^k * (eta k e)^2 +
      2*C*(3:ℝ)^(2*k)*(tau k e)^(2/3:ℝ) +
      (3:ℝ)^(2*k)*Real.sqrt C/(Real.sqrt (cutoff k e : ℝ)*tau k e) ≤
        e^2/(2*(k:ℝ)) := by sorry
