-- Prove2me | Theorems.Thm_GlobalTheory_DiagonalTimesLowerTriangular_main
-- name    : GlobalTheory.DiagonalTimesLowerTriangular.main
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:39.189368+00:00
-- url     : https://prove2.me/theorems/49086698-1a60-53bf-9d60-43942f478a7d
-- title:
--   Diagonal Times Lower Triangular: main
-- statement:
--   The Diagonal Times Lower Triangular construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DiagMulOfLower.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DiagMulOfLower.lean#L19-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiagMulOfLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DiagonalTimesLowerTriangular

theorem GlobalTheory.DiagonalTimesLowerTriangular.main : ∀ {K : Type} [inst : CommRing K] {s : ℕ} {a b : Matrix (Fin s) (Fin s) K}, (∀ (i j : Fin s), i < j → a i j = (0 : K)) → (∀ (i j : Fin s), i < j → b i j = (0 : K)) → ∀ (i : Fin s), (a * b) i i = a i i * b i i := by sorry
