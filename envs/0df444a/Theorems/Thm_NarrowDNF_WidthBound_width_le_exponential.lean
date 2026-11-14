-- Prove2me | Theorems.Thm_NarrowDNF_WidthBound_width_le_exponential
-- name    : NarrowDNF.WidthBound.width_le_exponential
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:23:44.722257+00:00
-- url     : https://prove2.me/theorems/86cc7a47-af5c-49a7-85ac-0b4c51591496
-- title:
--   The explicit certificate width has one absolute exponential bound
-- statement:
--   For $K>0$ and $0<\varepsilon<1$, set $c=\lceil K\rceil$, $d=\lceil4000c/\varepsilon\rceil$, $L=\exp(160000000000c^2/\varepsilon^2)$, and $W=\lceil4\,2^dL/\varepsilon\rceil$. Then
--   $$
--   W\le\exp\left(10^{13}\frac{(K+1)^2}{\varepsilon^2}\right).
--   $$
--   Thus the concrete width emerging from the structural and truncation arguments has the required dimension-independent form, with the explicit absolute constant $10^{13}$. All roundings and numerical constants in $W$ are retained.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/WidthBound.lean#L65-L108

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_WidthBound
import Theorems.Thm_NarrowDNF_WidthBound_ceil_width_le_exp

namespace NarrowDNF.WidthBound
end NarrowDNF.WidthBound
noncomputable section
open NarrowDNF
open NarrowDNF.WidthBound

theorem NarrowDNF.WidthBound.width_le_exponential {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) (hε1 : ε < 1) :
    (width K ε : ℝ) ≤ Real.exp (absoluteConstant * (K + 1)^2 / ε^2) := by sorry
