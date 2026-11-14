-- Prove2me | Theorems.Thm_NarrowDNF_HatamiResidual_approxComponent_abs_mean_le
-- name    : NarrowDNF.HatamiResidual.approxComponent_abs_mean_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:24:56.483533+00:00
-- url     : https://prove2.me/theorems/c9d3d25e-5ef0-4bd2-9ebe-7156c6d027ed
-- title:
--   Global absolute mean of an adaptive Boolean component
-- statement:
--   Let $I$ be finite, $0<p<1$, $f$ Boolean, and $J$ a local activation family. For a support $S$, write $F_S$ for the biased Fourier component of the $0/1$ encoding of $f$, and $\widetilde F_S=E_p[F_S\mid\mathcal F_{J_S}]$. Then
--   $$E_p[|\widetilde F_S|]\le2^{3|S|}p^{|S|}.$$
--   The estimate holds for every support and every such activation family. Its explicit degree factor supplies the coefficient needed in the corrected overlap and cross-term estimates.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiResidual.lean#L443-L479

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_HatamiActivation
import Definitions.Def_NarrowDNF_HatamiResidual
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_Fourier_character_abs_mean
import Theorems.Thm_NarrowDNF_Fourier_coefficient_bool_abs_le
import Theorems.Thm_NarrowDNF_HatamiResidual_approxComponent_abs_le

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier

namespace NarrowDNF.HatamiActivation
end NarrowDNF.HatamiActivation

namespace NarrowDNF.HatamiResidual
end NarrowDNF.HatamiResidual

namespace NarrowDNF.Influence
end NarrowDNF.Influence

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.HatamiResidual
open ProductMeasure
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.HatamiResidual.approxComponent_abs_mean_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Activation ι) (f : Cube ι → Bool) (S : Finset ι) :
    expectation p (fun x => |approxComponent p J (fun y => Influence.boolValue (f y)) S x|) ≤
      (2 : ℝ)^(3*S.card) * p^S.card := by sorry
