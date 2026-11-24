-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_CyclicMass_map_mk
-- name    : GlobalTheory.CuspGL.CyclicMass.map_mk
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:29:33.120404+00:00
-- url     : https://prove2.me/theorems/1a851f1c-5b25-4571-803e-1bad37e0aea6
-- title:
--   Cyclic Mass: map mk
-- statement:
--   The Cyclic Mass construction uses the map mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EndomorphismMassOfCharpolyCardCyclicVectors.lean#L22-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EndomorphismMassOfCharpolyCardCyclicVectors.lean#L22-L33

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

theorem GlobalTheory.CuspGL.CyclicMass.map_mk {V : Type} [AddCommGroup V] [Module F V] (D : F[X]) (f : AdjoinRoot D →ₗ[F] V)
    (g : Module.End F V) (h : ∀ a, f (AdjoinRoot.root D * a) = g (f a)) (p : F[X]) :
    f (AdjoinRoot.mk D p) = aeval g p (f 1) := by sorry
