-- Prove2me | Theorems.Thm_GlobalTheory_T_pairing_kernel_le_of_saturated_submodule
-- name    : GlobalTheory.T.pairing_kernel_le_of_saturated_submodule
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-27T06:21:47.751263+00:00
-- url     : https://prove2.me/theorems/c6afcefa-3b95-5a7b-afb0-b29236ab24ab
-- title:
--   T: pairing kernel le of saturated submodule
-- statement:
--   The T construction uses the pairing kernel le of saturated submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PairingKernelLeOfSaturatedSubmoduleStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PairingKernelLeOfSaturatedSubmoduleStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PairingKernelLeOfSaturatedSubmodule
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PairingKernelLeOfSaturatedSubmoduleStatement
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_pair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.pairing_kernel_le_of_saturated_submodule : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J) (g : Fin 2) (a' : ZMod d), ¬ X.big g a' → ∀ U' : Fin X.n → I (1 - g) → C, X.SatIn (1 - g) a' U' → ∀ (N : ℕ) (ψ : Fin N → J g → C), (∀ ν κ, V.Ge 0 (ψ ν κ)) → (∀ ν κ, (X.G g).ty (Sum.inr κ) ≠ a' → ψ ν κ = 0) → IndepMod V ψ → (∀ ν b, V.MM (∑ κ : J g, ∑ k : I (1 - g), ψ ν κ * X.pair g κ k * U' b k)) → N ≤ X.j := by sorry
