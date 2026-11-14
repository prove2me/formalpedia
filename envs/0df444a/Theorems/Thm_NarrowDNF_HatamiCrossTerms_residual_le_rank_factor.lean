-- Prove2me | Theorems.Thm_NarrowDNF_HatamiCrossTerms_residual_le_rank_factor
-- name    : NarrowDNF.HatamiCrossTerms.residual_le_rank_factor
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:24:52.152297+00:00
-- url     : https://prove2.me/theorems/e8d27dc3-5a9f-4387-8493-604c76a311aa
-- title:
--   Assembling residual errors with a covering set of ranks
-- statement:
--   On a finite cube, let $0\le p\le1$, $J$ be a local activation family, $f$ real valued, and $\mathcal A$ a finite family of supports. Let $\mathcal R\subseteq\mathbb N$ contain $|S|$ for every $S\in\mathcal A$. Write $F_S$ for Fourier components, $\widetilde F_S$ for their restricted-activation conditional approximations, and $\mathcal C=\sum_{S\ne R}\max(0,E_p[\widetilde F_S\widetilde F_R])$, summing over $\mathcal A$. Then
--   $$E_p\left[\left(\sum_{S\in\mathcal A}(F_S-\widetilde F_S)\right)^2\right]\le|\mathcal R|\left(\sum_{S\in\mathcal A}E_p[(F_S-\widetilde F_S)^2]+\mathcal C\right).$$
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiCrossTerms.lean#L398-L423

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
import Theorems.Thm_NarrowDNF_HatamiCrossTerms_rank_group_residual_le
import Theorems.Thm_NarrowDNF_RankGrouping_weighted_squared_sum_le_rank_groups

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

namespace NarrowDNF.RankGrouping
end NarrowDNF.RankGrouping
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.HatamiCrossTerms
open ProductMeasure HatamiResidual HatamiActivation
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.HatamiCrossTerms.residual_le_rank_factor {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (J : Activation ι) (f : Cube ι → ℝ) (A : Finset (Finset ι))
    (ranks : Finset ℕ) (hcover : ∀ S ∈ A, S.card ∈ ranks) :
    ConditionalExpectation.squaredError (weight p) (truncated p f A) (approxTruncated p J f A) ≤
      (ranks.card : ℝ) * ((∑ S ∈ A, ConditionalExpectation.squaredError (weight p)
        (Fourier.component p f S) (approxComponent p J f S)) + crossEnvelope p J f A) := by sorry
