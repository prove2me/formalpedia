-- Prove2me | Theorems.Thm_GlobalTheory_PerfectPairing_isReduced_rep
-- name    : GlobalTheory.PerfectPairing.isReduced_rep
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T18:19:40.89244+00:00
-- url     : https://prove2.me/theorems/30a4d893-9a5e-4859-9320-d326fce7d774
-- title:
--   Perfect Pairing: is Reduced rep
-- statement:
--   The Perfect Pairing construction uses the is Reduced rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CubWeilPerfectOfGeneric.lean#L73-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CubWeilPerfectOfGeneric.lean#L73-L95

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

theorem GlobalTheory.PerfectPairing.isReduced_rep {A : Over (Sp O)} [GrpObj A] [IsCommMonObj A] {n : ℕ} {H : Type} [CommRing H] [Algebra O H]
    [Module.Finite O H] {y : specO O H ⟶ A} (hy : y ^ n = 1)
    (hu : ∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ A), z ^ n = 1 →
      ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra O F] (hn : (n : F) ≠ 0) : _root_.IsReduced (F ⊗[O] H) := by sorry
