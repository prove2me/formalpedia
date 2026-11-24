-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_sUnits_union_sup_finSq_eq_top
-- name    : GlobalTheory.QNorm.sUnits_union_sup_finSq_eq_top
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:41:51.516044+00:00
-- url     : https://prove2.me/theorems/90c329b1-1639-4438-9299-2de68b91ff68
-- title:
--   QNorm: s Units union sup fin Sq eq top
-- statement:
--   The QNorm construction uses the s Units union sup fin Sq eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SUnitsUnionSupLocalSquaresEqTop.lean#L10-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SUnitsUnionSupLocalSquaresEqTop.lean#L10-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareMulOfNonsquareUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitValuationEqOfAdm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsUnionSupLocalSquaresEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm

theorem GlobalTheory.QNorm.sUnits_union_sup_finSq_eq_top :
    ∀ (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))] (S T : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → Disjoint S T → (∀ A : Finset (HeightOneSpectrum (𝓞 F)), ∃ u ∈ sUnits F S, ∀ v ∈ T, (IsSquare (algebraMap F (v.adicCompletion F) (u : F)) ↔ v ∉ A)) → sUnits F (S ∪ T) ⊔ finSq F T = ⊤ := by sorry
