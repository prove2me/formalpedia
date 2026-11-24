-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_Defect_evenNorms_of_le_four
-- name    : GlobalTheory.QNorm.Defect.evenNorms_of_le_four
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:43:15.56823+00:00
-- url     : https://prove2.me/theorems/818767ad-576b-49c0-be92-52280d1c00fa
-- title:
--   Defect: even Norms of le four
-- statement:
--   The Defect construction uses the even Norms of le four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsNormalFormNonsquareAdicCompletion.lean#L29-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsNormalFormNonsquareAdicCompletion.lean#L29-L61

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
open GlobalTheory.QNorm.Defect
variable {K : Type} [Field K] (w : Valuation K ℤᵐ⁰)

theorem GlobalTheory.QNorm.Defect.evenNorms_of_le_four (h2 : (2 : K) ≠ 0)
    (hsq : ∀ x : K, w (x - 1) < w 4 → IsSquare x) (δ : K) (hδ : w δ = 1) (hns : ¬ IsSquare δ)
    (h : w (δ - 1) ≤ w 4) : EvenNorms w δ := by sorry
