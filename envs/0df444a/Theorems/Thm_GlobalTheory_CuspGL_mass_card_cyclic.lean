-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_mass_card_cyclic
-- name    : GlobalTheory.CuspGL.mass_card_cyclic
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:32:54.935794+00:00
-- url     : https://prove2.me/theorems/44ce6e4d-aed6-4ebc-9bf9-185c1600f64d
-- title:
--   Cusp GL: mass card cyclic
-- statement:
--   The Cusp GL construction uses the mass card cyclic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EndomorphismMassOfCharpolyCardCyclicVectors.lean#L112-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EndomorphismMassOfCharpolyCardCyclicVectors.lean#L112-L131

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassOfCharpolyCardCyclicVectors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
noncomputable section
open GlobalTheory GlobalTheory.CuspGL

theorem GlobalTheory.CuspGL.mass_card_cyclic (F : Type) [Field F] [Finite F] (D : F[X]) (hD : D.Monic) :
    mass (fun g : Module.End F (Fin D.natDegree → F) =>
      (Nat.card {v : Fin D.natDegree → F // ∀ U : Submodule F (Fin D.natDegree → F),
        (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤} : ℂ)) D = glCard F D.natDegree := by sorry
