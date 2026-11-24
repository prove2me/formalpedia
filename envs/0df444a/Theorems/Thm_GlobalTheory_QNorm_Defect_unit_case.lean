-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_Defect_unit_case
-- name    : GlobalTheory.QNorm.Defect.unit_case
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:02:50.887658+00:00
-- url     : https://prove2.me/theorems/2263c908-2fe3-43a8-b9f9-e280a793461f
-- title:
--   Defect: unit case
-- statement:
--   The Defect construction uses the unit case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsNormalFormNonsquareAdicCompletion.lean#L71-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsNormalFormNonsquareAdicCompletion.lean#L71-L124

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

theorem GlobalTheory.QNorm.Defect.unit_case (h2 : (2 : K) ≠ 0) (π : K) (hπ : w π = WithZero.exp (-1))
    (hsq : ∀ x : K, w (x - 1) < w 4 → IsSquare x)
    (hres : w 2 < 1 → ∀ x : K, w x ≤ 1 → ∃ y : K, w y ≤ 1 ∧ w (x - y ^ 2) < 1)
    (m : ℤ) (hm : w 4 = WithZero.exp m) (N : ℕ) :
    ∀ δ : K, w δ = 1 → ¬ IsSquare δ → w (δ - 1) ≤ WithZero.exp (m + N) →
      ∃ c : K, c ≠ 0 ∧ ((w (δ * c ^ 2) = 1 ∧ w 4 < w (δ * c ^ 2 - 1) ∧
        ∃ n : ℤ, w (δ * c ^ 2 - 1) = WithZero.exp (2 * n + 1)) ∨ EvenNorms w (δ * c ^ 2)) := by sorry
