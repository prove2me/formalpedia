-- Prove2me | Theorems.Thm_NarrowDNF_HatamiCrossTerms_rank_group_residual_le
-- name    : NarrowDNF.HatamiCrossTerms.rank_group_residual_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:21:46.076197+00:00
-- url     : https://prove2.me/theorems/f7dc2600-9532-4402-a0fd-ef5540a411c5
-- title:
--   Residual Gram estimate within one cardinality rank
-- statement:
--   Let $p\in\mathbb R$, $J$ be a local activation family on finite $I$, $f$ real valued, $\mathcal A$ a finite support family, and $r\in\mathbb N$. Write $F_S$ for the biased Fourier component, $\widetilde F_S$ for its conditional approximation using $J_S$, $D_S=\sum_xw_p(x)(F_S(x)-\widetilde F_S(x))^2$, and $c_{SR}=\max(0,\sum_xw_p(x)\widetilde F_S(x)\widetilde F_R(x))$ for $S\ne R$, with $c_{SS}=0$. Then
--   $$\sum_xw_p(x)\left(\sum_{\substack{S\in\mathcal A\\|S|=r}}(F_S-\widetilde F_S)(x)\right)^2\le\sum_{\substack{S\in\mathcal A\\|S|=r}}\left(D_S+\sum_{R\in\mathcal A}c_{SR}\right).$$
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiCrossTerms.lean#L354-L396

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
import Definitions.Def_NarrowDNF_HatamiResidual
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Definitions.Def_NarrowDNF_ResidualGram
import Theorems.Thm_NarrowDNF_Activation_sameAtom_of_active_subset_of_agree
import Theorems.Thm_NarrowDNF_ConditionalExpectation_adaptiveCode_eq_iff
import Theorems.Thm_NarrowDNF_HatamiResidual_coordinateMean_eq_of_local
import Theorems.Thm_NarrowDNF_ProductMeasure_expectation_split
import Theorems.Thm_NarrowDNF_ResidualGram_residual_square_sum

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

theorem NarrowDNF.HatamiCrossTerms.rank_group_residual_le (p : ℝ) (J : Activation ι) (f : Cube ι → ℝ)
    (A : Finset (Finset ι)) (r : ℕ) :
    expectation p (fun x => (∑ S ∈ A with S.card = r,
      (Fourier.component p f S x - approxComponent p J f S x))^2) ≤
    ∑ S ∈ A with S.card = r,
      (ConditionalExpectation.squaredError (weight p) (Fourier.component p f S) (approxComponent p J f S) +
      ∑ R ∈ A, if S = R then 0 else
        max 0 (expectation p (fun x => approxComponent p J f S x * approxComponent p J f R x))) := by sorry
