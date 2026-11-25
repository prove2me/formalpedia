-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_dOne_glob_eq_wsum
-- name    : GlobalTheory.AbCoh.dOne_glob_eq_wsum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:18:49.514868+00:00
-- url     : https://prove2.me/theorems/0b9a990e-5c3f-4739-b821-abe7e60d48bc
-- title:
--   Ab Coh: d One glob eq wsum
-- statement:
--   The Ab Coh construction uses the d One glob eq wsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExteriorDerivGlobalOneFormEqSumWedge.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExteriorDerivGlobalOneFormEqSumWedge.lean#L12-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlobalTwoFormEqSumWedgeGlobalOneForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExteriorDerivGlobalOneFormEqSumWedge
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

theorem GlobalTheory.AbCoh.dOne_glob_eq_wsum : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    HasFrame F → CohomZeroIsConstants F → ∀ w : Glob1 F, ∃ (n : ℕ) (u v : Fin n → Glob1 F), ClRel F w u v := by sorry
