-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_twoForm_exists_pow_smul_eq_zero_of_algHom
-- name    : GlobalTheory.CechDR.twoForm_exists_pow_smul_eq_zero_of_algHom
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:59:16.292802+00:00
-- url     : https://prove2.me/theorems/2e184c2d-9774-4484-ac58-40731b667940
-- title:
--   Cech DR: two Form exists pow smul eq zero of alg Hom
-- statement:
--   The Cech DR construction uses the two Form exists pow smul eq zero of alg Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TwoFormExistsPowSmulEqZeroOfIsLocalization.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TwoFormExistsPowSmulEqZeroOfIsLocalization.lean#L46-L52

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

theorem GlobalTheory.CechDR.twoForm_exists_pow_smul_eq_zero_of_algHom {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (c : A)
    (hc : @IsLocalization.Away A _ c B _ f.toRingHom.toAlgebra) (x : Om R A 2)
    (hx : (SemiHom.of_algHom f).mOm 2 x = 0) : ∃ n : ℕ, c ^ n • x = 0 := by sorry
