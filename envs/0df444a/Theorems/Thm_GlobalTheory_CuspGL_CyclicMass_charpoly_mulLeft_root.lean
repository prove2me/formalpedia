-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_CyclicMass_charpoly_mulLeft_root
-- name    : GlobalTheory.CuspGL.CyclicMass.charpoly_mulLeft_root
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:29:32.511636+00:00
-- url     : https://prove2.me/theorems/b1a1b67d-ddd0-4bfe-abf7-3b89cb8fe5f9
-- title:
--   Cyclic Mass: charpoly mul Left root
-- statement:
--   The Cyclic Mass construction uses the charpoly mul Left root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EndomorphismMassOfCharpolyCardCyclicVectors.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EndomorphismMassOfCharpolyCardCyclicVectors.lean#L12-L20

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

theorem GlobalTheory.CuspGL.CyclicMass.charpoly_mulLeft_root (D : F[X]) (hD : D.Monic) [FiniteDimensional F (AdjoinRoot D)] :
    LinearMap.charpoly (LinearMap.mulLeft F (AdjoinRoot.root D)) = D := by sorry
