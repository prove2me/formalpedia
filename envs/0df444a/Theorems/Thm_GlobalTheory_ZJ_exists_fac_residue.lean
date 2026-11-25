-- Prove2me | Theorems.Thm_GlobalTheory_ZJ_exists_fac_residue
-- name    : GlobalTheory.ZJ.exists_fac_residue
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:30:47.662313+00:00
-- url     : https://prove2.me/theorems/81f6ba12-5e67-4128-b923-28c07faacd67
-- title:
--   ZJ: exists fac residue
-- statement:
--   The ZJ construction uses the exists fac residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FibreLawOfTestCartesian.lean#L34-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FibreLawOfTestCartesian.lean#L34-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusPointEqOneOfAxes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FibreLawOfTestCartesian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ

theorem GlobalTheory.ZJ.exists_fac_residue (V K : Type) [CommRing V] [IsLocalRing V] [Field K] (r : Sp K ⟶ Sp V)
    (hr : Set.range r = {IsLocalRing.closedPoint V}) :
    ∃ s : Sp K ⟶ Sp (IsLocalRing.ResidueField V), s ≫ spMap (IsLocalRing.residue V) = r := by sorry
