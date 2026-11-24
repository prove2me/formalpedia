-- Prove2me | Theorems.Thm_GlobalTheory_ValIwasawa_iwasawa_matrix
-- name    : GlobalTheory.ValIwasawa.iwasawa_matrix
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:49:59.956919+00:00
-- url     : https://prove2.me/theorems/dec15be8-bff8-4fbc-8d3c-0e0c9096b397
-- title:
--   Val Iwasawa: iwasawa matrix
-- statement:
--   The Val Iwasawa construction uses the iwasawa matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOfValILeOne.lean#L78-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOfValILeOne.lean#L78-L131

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOfValILeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ValIwasawa
open Matrix
variable {V F : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]

theorem GlobalTheory.ValIwasawa.iwasawa_matrix : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) F), A.det ≠ 0 →
    ∃ (k : Matrix (Fin n) (Fin n) V) (U : Matrix (Fin n) (Fin n) F), IsUnit k.det ∧ U.BlockTriangular id ∧
      (∀ i, U i i ≠ 0) ∧ A = k.map (algebraMap V F) * U
  := by sorry
