-- Prove2me | Theorems.Thm_GlobalTheory_PerfectPairing_val_one_iff
-- name    : GlobalTheory.PerfectPairing.val_one_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T18:17:34.44658+00:00
-- url     : https://prove2.me/theorems/8583ac1a-762f-48d3-8213-8b0789918ade
-- title:
--   Perfect Pairing: val one iff
-- statement:
--   The Perfect Pairing construction uses the val one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CubWeilPerfectOfGeneric.lean#L129-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CubWeilPerfectOfGeneric.lean#L129-L133

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubWeilOneLeft
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsReducedTorsionGeometricFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinRepExistsIsPullbackSpec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAlgHomLocalizationAugmentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CardAlgHomReducedTraceSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsUnitDetPairingOfBicharacterOfDvdTraceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubWeilPerfectOfGeneric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.PerfectPairing
variable {O : Type} [CommRing O]
variable {A : Over (Sp O)} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L) (n : ℕ)
  {S S' : Type} [CommRing S] [Algebra O S] [CommRing S'] [Algebra O S']
variable {c n} {x x' y y' : specO O S ⟶ A} {s s' : S}

theorem GlobalTheory.PerfectPairing.val_one_iff : Val c n x y 1 ↔ GlobalTheory.UU.CubWeil c n x y 1 := by sorry
