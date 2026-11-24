-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_torus_orthogonality
-- name    : GlobalTheory.CuspGL.torus_orthogonality
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:08.496038+00:00
-- url     : https://prove2.me/theorems/7f1709ba-37a4-4ec2-8ac8-cbdbead3c84c
-- title:
--   Cusp GL: torus orthogonality
-- statement:
--   The Cusp GL construction uses the torus orthogonality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FrobeniusTorusCharacterOrthogonality.lean#L66-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FrobeniusTorusCharacterOrthogonality.lean#L66-L92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FrobeniusTorusCharacterOrthogonality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL

theorem GlobalTheory.CuspGL.torus_orthogonality : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n : ℕ, 0 < n → (∃ ζ : AlgebraicClosure F, IsPrimitiveRoot ζ (Nat.card F ^ n - 1) ∧ IsPrimitiveRoot (θ ζ) (Nat.card F ^ n - 1)) ∧ ∀ k l : ℕ, ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, θ α ^ k * star (θ α ^ l) = if k ≡ l [MOD Nat.card F ^ n - 1] then ((Nat.card F ^ n - 1 : ℕ) : ℂ) else 0 := by sorry
