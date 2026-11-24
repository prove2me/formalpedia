-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_exists_local_nonnorm
-- name    : GlobalTheory.QNorm.exists_local_nonnorm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:04:42.693797+00:00
-- url     : https://prove2.me/theorems/8452aab6-3dbf-4ad5-b696-1813fd4d95a0
-- title:
--   QNorm: exists local nonnorm
-- statement:
--   The QNorm construction uses the exists local nonnorm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsLocalNonnormOfNonsquareAdicCompletion.lean#L80-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsLocalNonnormOfNonsquareAdicCompletion.lean#L80-L138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNormalFormNonsquareAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitEvenOrderQuadraticNormValuesOneModFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsGlobalUniformizerResidueRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsLocalNonnormOfNonsquareAdicCompletion
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
open NumberField IsDedekindDomain
open scoped WithZero

theorem GlobalTheory.QNorm.exists_local_nonnorm : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (δ : v.adicCompletion F), δ ≠ 0 → ¬ IsSquare δ →
    ∃ x : v.adicCompletion F, x ≠ 0 ∧ ¬ ∃ a b : v.adicCompletion F, x = a ^ 2 - δ * b ^ 2 := by sorry
