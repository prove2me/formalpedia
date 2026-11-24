-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_CyclicMass_card_pairs
-- name    : GlobalTheory.CuspGL.CyclicMass.card_pairs
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:29:27.589244+00:00
-- url     : https://prove2.me/theorems/1782a105-2b3e-45b5-a6e8-1a07f27dd4a5
-- title:
--   Cyclic Mass: card pairs
-- statement:
--   The Cyclic Mass construction uses the card pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EndomorphismMassOfCharpolyCardCyclicVectors.lean#L51-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EndomorphismMassOfCharpolyCardCyclicVectors.lean#L51-L106

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
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.CyclicMass
variable {F : Type} [Field F]

theorem GlobalTheory.CuspGL.CyclicMass.card_pairs {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (D : F[X]) (hD : D.Monic)
    (hV : Module.finrank F V = D.natDegree) :
    Nat.card (AdjoinRoot D ≃ₗ[F] V) =
      Nat.card (Σ g : {g : Module.End F V // LinearMap.charpoly g = D},
        {v : V // ∀ U : Submodule F V, (∀ x ∈ U, g.1 x ∈ U) → v ∈ U → U = ⊤}) := by sorry
