-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_exists_monomial_basis_of_abByP
-- name    : GlobalTheory.CuspGL.exists_monomial_basis_of_abByP
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:32:24.194908+00:00
-- url     : https://prove2.me/theorems/503703c4-1d65-4faf-878f-263d7c356553
-- title:
--   Cusp GL: exists monomial basis of ab By P
-- statement:
--   The Cusp GL construction uses the exists monomial basis of ab By P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsMonomialBasisAbelianByPrimePower.lean#L39-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsMonomialBasisAbelianByPrimePower.lean#L39-L107

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsAbelianByPrimePowerGroupSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantEqTopOfIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsMonomialBasisOfImprimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsMonomialBasisAbelianByPrimePower
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

theorem GlobalTheory.CuspGL.exists_monomial_basis_of_abByP : ∀ (k : Type) [Field k] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) [IsAlgClosed k], AbByP G → (Nat.card G : k) ≠ 0 → ∃ (n : ℕ) (b : Module.Basis (Fin n) k V), ∀ (g : G) (i : Fin n), ∃ (j : Fin n) (c : k), ρ g (b i) = c • b j := by sorry
