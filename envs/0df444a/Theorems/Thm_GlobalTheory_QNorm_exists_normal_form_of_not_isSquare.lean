-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_exists_normal_form_of_not_isSquare
-- name    : GlobalTheory.QNorm.exists_normal_form_of_not_isSquare
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:02:37.348703+00:00
-- url     : https://prove2.me/theorems/da6563d3-26f0-4780-a2ca-6a52b200e2f0
-- title:
--   QNorm: exists normal form of not is Square
-- statement:
--   The QNorm construction uses the exists normal form of not is Square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsNormalFormNonsquareAdicCompletion.lean#L335-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsNormalFormNonsquareAdicCompletion.lean#L335-L377

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsGlobalUniformizerResidueRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSubSqLtOneOfTwoLtOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EvenOrderNormsOneAddFourMulOfNoRootStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitMulSqQuadraticDefectStepStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNormalFormNonsquareAdicCompletion
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

theorem GlobalTheory.QNorm.exists_normal_form_of_not_isSquare : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (δ : v.adicCompletion F), δ ≠ 0 → ¬ IsSquare δ → ∃ c : v.adicCompletion F, c ≠ 0 ∧ ((∃ n : ℤ, Valued.v (δ * c ^ 2) = WithZero.exp (2 * n + 1)) ∨ (Valued.v (δ * c ^ 2) = 1 ∧ Valued.v (4 : v.adicCompletion F) < Valued.v (δ * c ^ 2 - 1) ∧ ∃ n : ℤ, Valued.v (δ * c ^ 2 - 1) = WithZero.exp (2 * n + 1)) ∨ _root_.GlobalTheory.QNorm.EvenNorms Valued.v (δ * c ^ 2)) := by sorry
