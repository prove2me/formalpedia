-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_mOm_two_eq_exteriorPowerMapOver
-- name    : GlobalTheory.CechDR.mOm_two_eq_exteriorPowerMapOver
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:59:30.333278+00:00
-- url     : https://prove2.me/theorems/8725f105-99f0-4f16-ae80-681f6e3ea48a
-- title:
--   Cech DR: m Om two eq exterior Power Map Over
-- statement:
--   The Cech DR construction uses the m Om two eq exterior Power Map Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TwoFormExistsPowSmulEqZeroOfIsLocalization.lean#L11-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TwoFormExistsPowSmulEqZeroOfIsLocalization.lean#L11-L31

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

theorem GlobalTheory.CechDR.mOm_two_eq_exteriorPowerMapOver {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] (x : Om R A 2) :
    (SemiHom.of_algHom (IsScalarTower.toAlgHom R A B)).mOm 2 x =
      GlobalTheory.exteriorPowerMapOver B 2 (KaehlerDifferential.map R R A B) x := by sorry
