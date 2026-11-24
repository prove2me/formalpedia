-- Prove2me | Theorems.Thm_GlobalTheory_ParabVirt_parab_virt
-- name    : GlobalTheory.ParabVirt.parab_virt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:41:15.351907+00:00
-- url     : https://prove2.me/theorems/3d0180ea-f6f2-40eb-903b-31d8f94c5ecf
-- title:
--   Parab Virt: parab virt
-- statement:
--   The Parab Virt construction uses the parab virt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ParabolicInductionTrivialPreservesVirtualCharact.lean#L193-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ParabolicInductionTrivialPreservesVirtualCharact.lean#L193-L289

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ParabolicInductionTrivialPreservesVirtualCharact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
noncomputable section
open GlobalTheory GlobalTheory.ParabVirt
variable {F : Type} [Field F] {n : ℕ}
open Polynomial
variable {F : Type} [Field F] {n : ℕ}

theorem GlobalTheory.ParabVirt.parab_virt : ∀ (F : Type) [Field F] [Finite F] (Φ : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V], Module.End F V → ℂ), (∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V), Φ V' (e.conj g) = Φ V g) → ∀ a n : ℕ, (fun x : GL (Fin a) F => Φ (Fin a → F) (Matrix.toLin' (x : Matrix (Fin a) (Fin a) F))) ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ (GL (Fin a) F) → (fun x : GL (Fin n) F => ∑ᶠ W : {W : Submodule F (Fin n → F) // Module.finrank F W = a ∧ ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W}, Φ W.1 ((Matrix.toLin' (x : Matrix (Fin n) (Fin n) F)).restrict W.2.2)) ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ (GL (Fin n) F) := by sorry
