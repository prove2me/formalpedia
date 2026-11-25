-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_cupSum_eq_zero_iff_wsum_eq_zero
-- name    : GlobalTheory.AbCoh.cupSum_eq_zero_iff_wsum_eq_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:01:49.282839+00:00
-- url     : https://prove2.me/theorems/6246a39c-675d-4da5-ad5a-3c0cca8ec536
-- title:
--   Ab Coh: cup Sum eq zero iff wsum eq zero
-- statement:
--   The Ab Coh construction uses the cup Sum eq zero iff wsum eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CupSumClosedGlobalOneFormsEqZeroIffSumWedge.lean#L15-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CupSumClosedGlobalOneFormsEqZeroIffSumWedge.lean#L15-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CupSumClosedGlobalOneFormsEqZeroIffSumWedge
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_toO

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
open GlobalTheory GlobalTheory.AbCoh

theorem GlobalTheory.AbCoh.cupSum_eq_zero_iff_wsum_eq_zero (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (hc : Closed1 F = ⊤) (hs : Function.Surjective (toO F)) (n : ℕ)
    (u v : Fin n → Glob1 F) :
    ∑ k, cupHyp F (clAll F hc (u k)) (clAll F hc (v k)) = 0 ↔ wsum F u v = 0 := by sorry
