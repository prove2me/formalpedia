-- Prove2me | Theorems.Thm_GlobalTheory_ResDegPlace_exists_eq_of_nonneg
-- name    : GlobalTheory.ResDegPlace.exists_eq_of_nonneg
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:10:49.475197+00:00
-- url     : https://prove2.me/theorems/9b9ef0b6-1aca-4300-afa3-20f64f2ff12a
-- title:
--   Res Deg Place: exists eq of nonneg
-- statement:
--   The Res Deg Place construction uses the exists eq of nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FdegEqFinrankResidueField.lean#L53-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FdegEqFinrankResidueField.lean#L53-L75

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

theorem GlobalTheory.ResDegPlace.exists_eq_of_nonneg {R F L : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field F] [Algebra R F] [IsFractionRing R F] [Field L] [Algebra F L] [Algebra R L]
    [IsScalarTower R F L] {w : AddValuation L (WithTop ℤ)} (hw : w ∈ ValPl.PlacesOver R L)
    (x : F) (hx : 0 ≤ w (algebraMap F L x)) : ∃ a : R, algebraMap R F a = x := by sorry
