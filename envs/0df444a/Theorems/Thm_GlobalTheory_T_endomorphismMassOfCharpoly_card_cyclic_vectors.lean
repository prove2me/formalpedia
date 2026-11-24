-- Prove2me | Theorems.Thm_GlobalTheory_T_endomorphismMassOfCharpoly_card_cyclic_vectors
-- name    : GlobalTheory.T.endomorphismMassOfCharpoly_card_cyclic_vectors
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:32:28.522289+00:00
-- url     : https://prove2.me/theorems/b01b1c7c-5159-4fed-9edb-7cc554e9b76b
-- title:
--   T: endomorphism Mass Of Charpoly card cyclic vectors
-- statement:
--   The T construction uses the endomorphism Mass Of Charpoly card cyclic vectors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EndomorphismMassOfCharpolyCardCyclicVectorsStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EndomorphismMassOfCharpolyCardCyclicVectorsStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassOfCharpolyCardCyclicVectors
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassOfCharpolyCardCyclicVectorsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.endomorphismMassOfCharpoly_card_cyclic_vectors : ∀ (F : Type) [Field F] [Finite F] (D : F[X]), D.Monic → mass (fun g : Module.End F (Fin D.natDegree → F) => (Nat.card {v : Fin D.natDegree → F // ∀ U : Submodule F (Fin D.natDegree → F), (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤} : ℂ)) D = glCard F D.natDegree := by sorry
