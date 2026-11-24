-- Prove2me | Theorems.Thm_GlobalTheory_SubspaceNumber_card_fibre
-- name    : GlobalTheory.SubspaceNumber.card_fibre
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:23:25.426855+00:00
-- url     : https://prove2.me/theorems/ff692181-bf72-4578-a94b-0e48bb3f2c58
-- title:
--   Subspace Number: card fibre
-- statement:
--   The Subspace Number construction uses the card fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CardSubspacesOfFinrankMulCardBases.lean#L7-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CardSubspacesOfFinrankMulCardBases.lean#L7-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesOfFinrankMulCardBases
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.SubspaceNumber

theorem GlobalTheory.SubspaceNumber.card_fibre {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (a : ℕ) (W : Submodule F V) (hW : Module.finrank F W = a) :
    Nat.card {s : {s : Fin a → V // LinearIndependent F s} //
      Submodule.span F (Set.range s.1) = W} = Nat.card {t : Fin a → W // LinearIndependent F t} := by sorry
