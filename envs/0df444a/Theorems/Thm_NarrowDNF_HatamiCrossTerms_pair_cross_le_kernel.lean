-- Prove2me | Theorems.Thm_NarrowDNF_HatamiCrossTerms_pair_cross_le_kernel
-- name    : NarrowDNF.HatamiCrossTerms.pair_cross_le_kernel
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:35:16.811194+00:00
-- url     : https://prove2.me/theorems/7fe776d8-fe9e-4b16-b8ee-85133932013f
-- title:
--   Pairwise adaptive correlation controlled by an inactive intersection
-- statement:
--   Let $f$ be Boolean on a finite cube, $0<p<1$, $J$ any local activation family, and $S\ne R$. Set $\widetilde F_S=E_p[F_S\mid\mathcal F_{J_S}]$ and similarly for $R$. For $K_J(T)=E_p[\mathbf1_{\neg J_T}/w_{p,T}^2]$, one has
--   $$E_p[\widetilde F_S\widetilde F_R]\le(2^{3|S|}p^{|S|})(2^{3|R|}p^{|R|})K_J(S\cap R).$$
--   Here $J_S$ retains exactly activations indexed by subsets of $S$, and $w_{p,T}$ is the marginal product mass on $T$.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiCrossTerms.lean#L53-L88

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
import Definitions.Def_NarrowDNF_ConditionalExpectation
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_HatamiActivation
import Definitions.Def_NarrowDNF_HatamiCrossTerms
import Definitions.Def_NarrowDNF_HatamiResidual
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_Activation_sameAtom_of_active_subset_of_agree
import Theorems.Thm_NarrowDNF_ConditionalExpectation_adaptiveCode_eq_iff
import Theorems.Thm_NarrowDNF_ConditionalExpectation_local_conditional_independence
import Theorems.Thm_NarrowDNF_HatamiResidual_approxComponent_abs_mean_le
import Theorems.Thm_NarrowDNF_HatamiResidual_approxComponent_conditional_zero_of_fires

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.ConditionalExpectation
end NarrowDNF.ConditionalExpectation

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

theorem NarrowDNF.HatamiCrossTerms.pair_cross_le_kernel {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Activation ι) (f : Cube ι → Bool) (S R : Finset ι) (hSR : S ≠ R) :
    expectation p (fun x => approxComponent p J (fun y => Influence.boolValue (f y)) S x *
      approxComponent p J (fun y => Influence.boolValue (f y)) R x) ≤
      ((2:ℝ)^(3*S.card) * p^S.card) * ((2:ℝ)^(3*R.card) * p^R.card) *
        inactiveKernel p J (S ∩ R) := by sorry
