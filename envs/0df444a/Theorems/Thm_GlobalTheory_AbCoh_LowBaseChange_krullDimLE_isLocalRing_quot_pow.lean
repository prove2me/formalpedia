-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_LowBaseChange_krullDimLE_isLocalRing_quot_pow
-- name    : GlobalTheory.AbCoh.LowBaseChange.krullDimLE_isLocalRing_quot_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:50:23.713617+00:00
-- url     : https://prove2.me/theorems/376a8641-1fa2-45a8-9827-23e58b5682af
-- title:
--   Low Base Change: krull Dim LE is Local Ring quot pow
-- statement:
--   The Low Base Change construction uses the krull Dim LE is Local Ring quot pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KrullDimLEIsLocalRingQuotPow.lean#L12-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KrullDimLEIsLocalRingQuotPow.lean#L12-L30

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

theorem GlobalTheory.AbCoh.LowBaseChange.krullDimLE_isLocalRing_quot_pow {R : Type} [CommRing R] (m : Ideal R)
    [hm : m.IsMaximal] (n : ℕ) :
    Ring.KrullDimLE 0 (R ⧸ m ^ (n + 1)) ∧ IsLocalRing (R ⧸ m ^ (n + 1)) := by sorry
