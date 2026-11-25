-- Prove2me | Theorems.Thm_GlobalTheory_EmbFrob_exists_pow_of_finite_field
-- name    : GlobalTheory.EmbFrob.exists_pow_of_finite_field
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:13:48.865851+00:00
-- url     : https://prove2.me/theorems/c4e3493b-0347-4a3c-aa6d-db2600c23c33
-- title:
--   Emb Frob: exists pow of finite field
-- statement:
--   The Emb Frob construction uses the exists pow of finite field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsPowOfFiniteField.lean#L13-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsPowOfFiniteField.lean#L13-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StAvDefs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueMaximalAbovePlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsPowOfFiniteField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory GlobalTheory.EmbFrob
open Polynomial

theorem GlobalTheory.EmbFrob.exists_pow_of_finite_field (p : ℕ) [Fact p.Prime] {F k : Type} [Field F] [Finite F]
    [Field k] [CharP k p] (f g : F →+* k) : ∃ i : ℕ, ∀ a : F, g a = f a ^ p ^ i := by sorry
