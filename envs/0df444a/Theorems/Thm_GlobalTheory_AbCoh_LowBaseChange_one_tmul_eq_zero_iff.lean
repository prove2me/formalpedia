-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_LowBaseChange_one_tmul_eq_zero_iff
-- name    : GlobalTheory.AbCoh.LowBaseChange.one_tmul_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:04:38.155098+00:00
-- url     : https://prove2.me/theorems/530123c7-2972-59fe-a356-4129ca764b41
-- title:
--   Low Base Change: one tmul eq zero iff
-- statement:
--   The Low Base Change construction uses the one tmul eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KrullDimLEIsLocalRingQuotPow.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KrullDimLEIsLocalRingQuotPow.lean#L34-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrullDimLEIsLocalRingQuotPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.LowBaseChange
variable {R : Type} [CommRing R]

theorem GlobalTheory.AbCoh.LowBaseChange.one_tmul_eq_zero_iff {M : Type} [AddCommGroup M] [Module R M] (I : Ideal R) (x : M) :
    (1 : R ⧸ I) ⊗ₜ[R] x = 0 ↔ x ∈ I • (⊤ : Submodule R M) := by sorry
