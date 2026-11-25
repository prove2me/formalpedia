-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_Wedge_alt2_apply
-- name    : GlobalTheory.AbCoh.Wedge.alt2_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:25:11.068218+00:00
-- url     : https://prove2.me/theorems/23215ce7-f919-484a-867d-4d34e7ea53bb
-- title:
--   Wedge: alt2 apply
-- statement:
--   The Wedge construction uses the alt2 apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WedgePropertyFromFibres.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WedgePropertyFromFibres.lean#L29-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafCohomologyPullbackCompCupIdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubsingletonOfResidueFieldFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WedgePropertyFromFibres
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
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.Wedge

theorem GlobalTheory.AbCoh.Wedge.alt2_apply {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] M →ₗ[R] N) (hf : ∀ x, f x x = 0) (v : Fin 2 → M) : alt2 f hf v = f (v 0) (v 1) := by sorry
