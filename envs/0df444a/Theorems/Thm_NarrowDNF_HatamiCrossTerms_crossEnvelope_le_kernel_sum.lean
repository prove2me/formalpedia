-- Prove2me | Theorems.Thm_NarrowDNF_HatamiCrossTerms_crossEnvelope_le_kernel_sum
-- name    : NarrowDNF.HatamiCrossTerms.crossEnvelope_le_kernel_sum
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:45:40.037111+00:00
-- url     : https://prove2.me/theorems/b6dacf17-f830-4d49-8851-c174d436903d
-- title:
--   Cross envelope bounded by weighted overlap kernels
-- statement:
--   Let $I$ be finite, $0<p<1$, $f$ Boolean, $J$ any local activation family, and $\mathcal A$ a finite support family with $|S|\le k$ for a real cutoff $k$. Write $\widetilde F_S=E_p[F_S\mid\mathcal F_{J_S}]$, and $K_J(T)=E_p[\mathbf1_{\neg J_T}/w_{p,T}^2]$, where $w_{p,T}$ is the marginal point mass. The off-diagonal envelope satisfies
--   $$\sum_{\substack{S,R\in\mathcal A\\S\ne R}}\max\{0,E_p[\widetilde F_S\widetilde F_R]\}\le2^{6k}\sum_{S,R\in\mathcal A}p^{|S|+|R|}K_J(S\cap R).$$
--   This replaces all adaptive correlations by a single nonnegative overlap sum.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiCrossTerms.lean#L263-L287

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
import Definitions.Def_NarrowDNF_HatamiCrossTerms
import Definitions.Def_NarrowDNF_HatamiResidual
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_HatamiCrossTerms_pair_cross_le_kernel

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

namespace NarrowDNF.HatamiCrossTerms
end NarrowDNF.HatamiCrossTerms

namespace NarrowDNF.HatamiResidual
end NarrowDNF.HatamiResidual

namespace NarrowDNF.Influence
end NarrowDNF.Influence

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.HatamiCrossTerms
open ProductMeasure HatamiResidual HatamiActivation
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.HatamiCrossTerms.crossEnvelope_le_kernel_sum {p k : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Activation ι) (f : Cube ι → Bool) (A : Finset (Finset ι))
    (hcard : ∀ S ∈ A, (S.card : ℝ) ≤ k) :
    crossEnvelope p J (fun x => Influence.boolValue (f x)) A ≤
      (2:ℝ)^(6*k) * ∑ S ∈ A, ∑ R ∈ A,
        p^S.card * p^R.card * inactiveKernel p J (S ∩ R) := by sorry
