-- Prove2me | Theorems.Thm_GlobalTheory_AbelianSumIdentityFourth_main
-- name    : GlobalTheory.AbelianSumIdentityFourth.main
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:54:36.757037+00:00
-- url     : https://prove2.me/theorems/7ed43fc9-e458-49b5-bc13-7aaccbac619f
-- title:
--   Abelian Sum Identity Fourth: main
-- statement:
--   The Abelian Sum Identity Fourth construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsMoreRest.lean#L7-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsMoreRest.lean#L7-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsMoreRest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AbelianSumIdentityFourth
open Matrix

theorem GlobalTheory.AbelianSumIdentityFourth.main : ∀ {A : Type} [inst : CommRing A] {n q : ℕ} (X Y : Matrix (Fin n) (Fin q) A) (RX RY : Matrix (Fin q) (Fin n) A) (a b a' b' : Fin q → A), RY * X = (1 : Matrix (Fin q) (Fin q) A) → RY * Y = (0 : Matrix (Fin q) (Fin q) A) → RX * X = (0 : Matrix (Fin q) (Fin q) A) → RX * Y = (1 : Matrix (Fin q) (Fin q) A) → (∀ (i : Fin q), a i + a' i + a i * a' i = (0 : A)) → (∀ (i : Fin q), b i + b' i + b i * b' i = (0 : A)) → ((1 : Matrix (Fin n) (Fin n) A) + X * Matrix.diagonal a * RY + Y * Matrix.diagonal b * RX) * ((1 : Matrix (Fin n) (Fin n) A) + X * Matrix.diagonal a' * RY + Y * Matrix.diagonal b' * RX) = (1 : Matrix (Fin n) (Fin n) A) := by sorry
