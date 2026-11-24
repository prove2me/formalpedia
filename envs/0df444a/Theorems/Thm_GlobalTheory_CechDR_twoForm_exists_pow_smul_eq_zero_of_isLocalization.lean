-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_twoForm_exists_pow_smul_eq_zero_of_isLocalization
-- name    : GlobalTheory.CechDR.twoForm_exists_pow_smul_eq_zero_of_isLocalization
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:59:07.551644+00:00
-- url     : https://prove2.me/theorems/26484c25-1719-4790-b64c-78f3d883440d
-- title:
--   Cech DR: two Form exists pow smul eq zero of is Localization
-- statement:
--   The Cech DR construction uses the two Form exists pow smul eq zero of is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TwoFormExistsPowSmulEqZeroOfIsLocalization.lean#L33-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TwoFormExistsPowSmulEqZeroOfIsLocalization.lean#L33-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwoFormExistsPowSmulEqZeroOfIsLocalization
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_of_algHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CechDR

theorem GlobalTheory.CechDR.twoForm_exists_pow_smul_eq_zero_of_isLocalization {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] (c : A)
    [IsLocalization.Away c B] (x : Om R A 2)
    (hx : (SemiHom.of_algHom (IsScalarTower.toAlgHom R A B)).mOm 2 x = 0) :
    ∃ n : ℕ, c ^ n • x = 0 := by sorry
