-- Prove2me | Theorems.Thm_NarrowDNF_HatamiInput_highDegreeReal_mass_le
-- name    : NarrowDNF.HatamiInput.highDegreeReal_mass_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:32:32.690109+00:00
-- url     : https://prove2.me/theorems/a33bd00a-6c3e-49b9-a46d-e240bd430a58
-- title:
--   Fourier mass above a real cutoff from resampling influence
-- statement:
--   Let $I$ be finite, $0<p<1$, $k>0$, and $f:\{0,1\}^I\to\{0,1\}$. Let $\widehat f_p(S)$ be the coefficients of its $0/1$ real encoding in the orthonormal $p$-biased Fourier basis. If $I_p(f)$ denotes total influence under independent resampling of one coordinate, then
--   $$\sum_{\substack{S\subseteq I\\|S|>k}}\widehat f_p(S)^2\le\frac{I_p(f)}{2k}.$$
--   The cutoff is real, rather than restricted to integral degrees. This is the high-frequency contribution to the paper's first Fourier pruning step.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiInput.lean#L24-L45

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_FiberShift
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_HatamiActivation
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_Fourier_inner_parseval
import Theorems.Thm_NarrowDNF_ProductMeasure_expectation_split

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

namespace NarrowDNF.HatamiInput
end NarrowDNF.HatamiInput

namespace NarrowDNF.Influence
end NarrowDNF.Influence

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.HatamiInput
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.HatamiInput.highDegreeReal_mass_le {p k : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hk : 0 < k) (f : Cube ι → Bool) :
    (∑ S : Finset ι, if k < (S.card : ℝ) then
      Fourier.setCoefficient p (fun x => Influence.boolValue (f x)) S ^ 2 else 0) ≤
        Influence.totalInfluence p f / (2*k) := by sorry
