-- Prove2me | Theorems.Thm_GlobalTheory_Frames_spMap_epsScaleR_comp
-- name    : GlobalTheory.Frames.spMap_epsScaleR_comp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:40:33.443331+00:00
-- url     : https://prove2.me/theorems/cc640216-f1a9-4125-a579-353bef23589e
-- title:
--   Frames: sp Map eps Scale R comp
-- statement:
--   The Frames construction uses the sp Map eps Scale R comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LieBasisIffTangentBasisPullbackUniversal.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LieBasisIffTangentBasisPullbackUniversal.lean#L15-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LieBasisIffTangentBasisPullbackUniversal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Frames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem GlobalTheory.Frames.spMap_epsScaleR_comp {S : Type} [CommRing S] (c : S) :
    spMap (epsScaleR c) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap S (DualNumber S)) := by sorry
