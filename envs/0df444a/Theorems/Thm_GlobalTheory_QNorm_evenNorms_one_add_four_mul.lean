-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_evenNorms_one_add_four_mul
-- name    : GlobalTheory.QNorm.evenNorms_one_add_four_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:49.297311+00:00
-- url     : https://prove2.me/theorems/aa8cbb51-369f-4568-a207-a0c011349dd3
-- title:
--   QNorm: even Norms one add four mul
-- statement:
--   The QNorm construction uses the even Norms one add four mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/EvenOrderNormsOneAddFourMulOfNoRoot.lean#L20-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/EvenOrderNormsOneAddFourMulOfNoRoot.lean#L20-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EvenOrderNormsOneAddFourMulOfNoRoot
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

theorem GlobalTheory.QNorm.evenNorms_one_add_four_mul :
    ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (ρ : K), (2 : K) ≠ 0 → w ρ ≤ 1 →
      (∀ x : K, w x ≤ 1 → w (x ^ 2 + x - ρ) = 1) →
        _root_.GlobalTheory.QNorm.EvenNorms w (1 + 4 * ρ) := by sorry
