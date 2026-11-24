-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_monomial_basis_abelianByPrimePower
-- name    : GlobalTheory.T.exists_monomial_basis_abelianByPrimePower
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:37:07.483478+00:00
-- url     : https://prove2.me/theorems/28643c6f-4b09-4a0a-8fe1-7aefd18eb1fb
-- title:
--   T: exists monomial basis abelian By Prime Power
-- statement:
--   The T construction uses the exists monomial basis abelian By Prime Power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsMonomialBasisAbelianByPrimePowerStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsMonomialBasisAbelianByPrimePowerStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsMonomialBasisAbelianByPrimePower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsMonomialBasisAbelianByPrimePowerStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_monomial_basis_abelianByPrimePower : ∀ (k : Type) [Field k] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) [IsAlgClosed k], AbByP G → (Nat.card G : k) ≠ 0 → ∃ (n : ℕ) (b : Module.Basis (Fin n) k V), ∀ (g : G) (i : Fin n), ∃ (j : Fin n) (c : k), ρ g (b i) = c • b j := by sorry
