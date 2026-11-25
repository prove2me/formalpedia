-- Prove2me | Theorems.Thm_GlobalTheory_LieLoc_exists_univChart_away
-- name    : GlobalTheory.LieLoc.exists_univChart_away
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:47:10.350539+00:00
-- url     : https://prove2.me/theorems/8922f273-0b01-5ec6-af7b-042136ed644d
-- title:
--   Lie Loc: exists univ Chart away
-- statement:
--   The Lie Loc construction uses the exists univ Chart away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/UnivChartOfStandardSmooth.lean#L169-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/UnivChartOfStandardSmooth.lean#L169-L187

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnivChartOfStandardSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LieLoc
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Chart
variable {R : Type} [CommRing R]

theorem GlobalTheory.LieLoc.exists_univChart_away (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (n : ℕ)
    (h : SmoothOfRelativeDimension n G.hom) (p : PrimeSpectrum R) :
    ∃ r ∉ p.asIdeal, ∃ x : ∀ m : ℕ, sp (R₀ := Localization.Away r)
      (JetR (Localization.Away r) (Fin n) m) ⟶ (Over.pullback (fB R (Localization.Away r))).obj G,
      IsUnivChart _ n x := by sorry
