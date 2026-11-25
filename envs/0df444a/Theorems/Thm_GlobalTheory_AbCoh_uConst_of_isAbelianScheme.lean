-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_uConst_of_isAbelianScheme
-- name    : GlobalTheory.AbCoh.uConst_of_isAbelianScheme
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:09:42.793376+00:00
-- url     : https://prove2.me/theorems/2531bd24-0e5e-44a2-aecd-4cfe5bbe22bf
-- title:
--   Ab Coh: u Const of is Abelian Scheme
-- statement:
--   The Ab Coh construction uses the u Const of is Abelian Scheme property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlobalFunctionsConstantAfterBaseChangeOfAbelianS.lean#L17-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlobalFunctionsConstantAfterBaseChangeOfAbelianS.lean#L17-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_OneTmulNeZeroOfDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsNoetherianModelOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlobalFunctionsConstantAfterBaseChangeOfAbelianS
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
open GlobalTheory GlobalTheory.AbCoh
open Opposite TopologicalSpace

theorem GlobalTheory.AbCoh.uConst_of_isAbelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → UConst A.hom := by sorry
