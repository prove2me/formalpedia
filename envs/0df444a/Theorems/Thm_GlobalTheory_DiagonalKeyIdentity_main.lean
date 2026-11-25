-- Prove2me | Theorems.Thm_GlobalTheory_DiagonalKeyIdentity_main
-- name    : GlobalTheory.DiagonalKeyIdentity.main
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:52.045842+00:00
-- url     : https://prove2.me/theorems/2833b3e4-e75e-4d3c-b0aa-753255524a55
-- title:
--   Diagonal Key Identity: main
-- statement:
--   The Diagonal Key Identity construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DiagKey.lean#L15-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DiagKey.lean#L15-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiagKey
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DiagonalKeyIdentity
open Matrix

theorem GlobalTheory.DiagonalKeyIdentity.main : ∀ {A : Type} [inst : CommRing A] {n q : ℕ} (J : Matrix (Fin n) (Fin n) A) (X Xc Y Yc : Matrix (Fin n) (Fin q) A) (a b : Fin q → A), Matrix.transpose X * J * Xc = (0 : Matrix (Fin q) (Fin q) A) → Matrix.transpose X * J * Yc = (1 : Matrix (Fin q) (Fin q) A) → Matrix.transpose Y * J * Xc = (1 : Matrix (Fin q) (Fin q) A) → Matrix.transpose Y * J * Yc = (0 : Matrix (Fin q) (Fin q) A) → (∀ (i : Fin q), a i + b i + a i * b i = (0 : A)) → ((1 : Matrix (Fin n) (Fin n) A) + J * Yc * Matrix.diagonal a * Matrix.transpose X + J * Xc * Matrix.diagonal b * Matrix.transpose Y) * J * ((1 : Matrix (Fin n) (Fin n) A) + Xc * Matrix.diagonal a * (Matrix.transpose Y * J) + Yc * Matrix.diagonal b * (Matrix.transpose X * J)) = J := by sorry
