-- Prove2me | Theorems.Thm_GlobalTheory_PerfectPairing_algHom_eq_of_isUnit_det
-- name    : GlobalTheory.PerfectPairing.algHom_eq_of_isUnit_det
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T18:32:54.292437+00:00
-- url     : https://prove2.me/theorems/d43bc28c-cabb-5e6b-aecf-08a4ffc1d31a
-- title:
--   Perfect Pairing: alg Hom eq of is Unit det
-- statement:
--   The Perfect Pairing construction uses the alg Hom eq of is Unit det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CubWeilPerfectOfGeneric.lean#L172-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CubWeilPerfectOfGeneric.lean#L172-L194

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

theorem GlobalTheory.PerfectPairing.algHom_eq_of_isUnit_det {H S : Type} [CommRing H] [Algebra O H] [CommRing S] [Algebra O S] {r : ℕ}
    (b : Module.Basis (Fin r) O H) (D : Matrix (Fin r) (Fin r) O) (hD : IsUnit D.det) (φ φ' : H →ₐ[O] S)
    (h : ∑ i, ∑ j, algebraMap O (S ⊗[O] H) (D i j) * (φ (b i) ⊗ₜ[O] (1 : H)) * ((1 : S) ⊗ₜ[O] b j) =
      ∑ i, ∑ j, algebraMap O (S ⊗[O] H) (D i j) * (φ' (b i) ⊗ₜ[O] (1 : H)) * ((1 : S) ⊗ₜ[O] b j)) : φ = φ' := by sorry
