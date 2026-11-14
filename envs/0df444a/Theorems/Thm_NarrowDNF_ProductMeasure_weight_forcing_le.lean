-- Prove2me | Theorems.Thm_NarrowDNF_ProductMeasure_weight_forcing_le
-- name    : NarrowDNF.ProductMeasure.weight_forcing_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:15:30.928207+00:00
-- url     : https://prove2.me/theorems/7ebd3e1c-dd6b-4baf-9a88-a9a4c54ef257
-- title:
--   A point-mass bound for the effective forcing bias
-- statement:
--   Let $I$ be finite, $0\le p\le1$, and $x\in\{0,1\}^I$. If $w_p(x)=\prod_i(p\text{ if }x_i=1\text{ else }1-p)$, then
--   $$
--   w_{2p-p^2}(x)\le(2-p)^{|I|}w_p(x).
--   $$
--   The estimate uses multiplication rather than division by $w_p(x)$, so it remains valid at $p=0$ and $p=1$. Applied on an activation's coordinate set, the exponent counts that activation's arity rather than the ambient dimension.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/LoadTransport.lean#L32-L48

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.ProductMeasure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem NarrowDNF.ProductMeasure.weight_forcing_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ι → Bool) :
    weight (2 * p - p ^ 2) x ≤ (2 - p) ^ Fintype.card ι * weight p x := by sorry
