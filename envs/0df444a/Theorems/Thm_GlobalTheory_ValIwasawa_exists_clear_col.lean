-- Prove2me | Theorems.Thm_GlobalTheory_ValIwasawa_exists_clear_col
-- name    : GlobalTheory.ValIwasawa.exists_clear_col
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:50:15.074772+00:00
-- url     : https://prove2.me/theorems/300925d3-d2a4-42f4-94dd-1e5b12245684
-- title:
--   Val Iwasawa: exists clear col
-- statement:
--   The Val Iwasawa construction uses the exists clear col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOfValILeOne.lean#L19-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOfValILeOne.lean#L19-L76

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

theorem GlobalTheory.ValIwasawa.exists_clear_col {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (hA : A.det ≠ 0) :
    ∃ Q : Matrix (Fin (n + 1)) (Fin (n + 1)) V, IsUnit Q.det ∧
      ∀ i : Fin n, (Q.map (algebraMap V F) * A) i.succ 0 = 0 := by sorry
