-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_nonempty_model_of_quasiIso
-- name    : GlobalTheory.AbCoh.nonempty_model_of_quasiIso
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:55:59.352976+00:00
-- url     : https://prove2.me/theorems/6664cdc9-f5d0-4b87-ab17-136d4dd37c83
-- title:
--   Ab Coh: nonempty model of quasi Iso
-- statement:
--   The Ab Coh construction uses the nonempty model of quasi Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NonemptyStructureSheafCohomologyModelOfQuasiIso.lean#L86-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NonemptyStructureSheafCohomologyModelOfQuasiIso.lean#L86-L155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NonemptyStructureSheafCohomologyModelOfQuasiIso
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbCoh

theorem GlobalTheory.AbCoh.nonempty_model_of_quasiIso : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (K C : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ C), (∀ (S : Type) [CommRing S] [Algebra R S],
      QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R S)).mapHomologicalComplex _).map φ)) →
    Model s C → Nonempty (Model s K) := by sorry
