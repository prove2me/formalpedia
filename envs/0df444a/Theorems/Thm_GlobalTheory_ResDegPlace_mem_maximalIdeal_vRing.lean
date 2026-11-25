-- Prove2me | Theorems.Thm_GlobalTheory_ResDegPlace_mem_maximalIdeal_vRing
-- name    : GlobalTheory.ResDegPlace.mem_maximalIdeal_vRing
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:10:45.056151+00:00
-- url     : https://prove2.me/theorems/957109ff-231e-4b48-818b-d0e2d37bfac6
-- title:
--   Res Deg Place: mem maximal Ideal v Ring
-- statement:
--   The Res Deg Place construction uses the mem maximal Ideal v Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FdegEqFinrankResidueField.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FdegEqFinrankResidueField.lean#L46-L51

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAE
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FdegEqFinrankResidueField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct
open GlobalTheory GlobalTheory.ResDegPlace
open IsLocalRing

theorem GlobalTheory.ResDegPlace.mem_maximalIdeal_vRing {L : Type*} [Field L] (w : AddValuation L (WithTop ℤ))
    (x : vRing w) : x ∈ maximalIdeal (vRing w) ↔ 0 < w (x : L) := by sorry
