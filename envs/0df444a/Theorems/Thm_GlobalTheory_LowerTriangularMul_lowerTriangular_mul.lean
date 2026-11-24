-- Prove2me | Theorems.Thm_GlobalTheory_LowerTriangularMul_lowerTriangular_mul
-- name    : GlobalTheory.LowerTriangularMul.lowerTriangular_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:16:51.796324+00:00
-- url     : https://prove2.me/theorems/edc2a1f7-787e-468f-a10a-163292dec1d6
-- title:
--   Lower Triangular Mul: lower Triangular mul
-- statement:
--   The Lower Triangular Mul construction uses the lower Triangular mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LowerTriangularMul.lean#L5-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LowerTriangularMul.lean#L5-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LowerTriangularMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LowerTriangularMul

theorem GlobalTheory.LowerTriangularMul.lowerTriangular_mul {S : Type} [CommRing S] {n : ℕ} (A B : Matrix (Fin n) (Fin n) S)
    (hA : ∀ (i j : Fin n), i < j → A i j = (0 : S))
    (hB : ∀ (i j : Fin n), i < j → B i j = (0 : S)) :
    ∀ (i j : Fin n), i < j → (A * B) i j = (0 : S) := by sorry
