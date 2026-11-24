-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_psi_one
-- name    : GlobalTheory.CuspGL.psi_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:22.466129+00:00
-- url     : https://prove2.me/theorems/86130dc7-a48f-4e41-bf41-4ea344406b25
-- title:
--   Cusp GL: psi one
-- statement:
--   The Cusp GL construction uses the psi one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvariantSubspaceMobiusInverseOneProdIco.lean#L74-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvariantSubspaceMobiusInverseOneProdIco.lean#L74-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumGaussianMulProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesOfFinrankMulCardBasesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseOneProdIco
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL

theorem GlobalTheory.CuspGL.psi_one (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (s : F[X] → ℂ) (hs : ∀ j : ℕ, s ((X - C 1) ^ j) = j) (h : 0 < Module.finrank F V) :
    psi s V 1 = ∏ i ∈ Finset.Ico 1 (Module.finrank F V), (1 - (Nat.card F : ℂ) ^ i) := by sorry
