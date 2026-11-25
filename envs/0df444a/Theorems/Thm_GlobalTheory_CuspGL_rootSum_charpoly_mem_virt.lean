-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_rootSum_charpoly_mem_virt
-- name    : GlobalTheory.CuspGL.rootSum_charpoly_mem_virt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:21:11.688121+00:00
-- url     : https://prove2.me/theorems/c82cc7d5-9eaa-4471-9ee8-bec40abafdf0
-- title:
--   Cusp GL: root Sum charpoly mem virt
-- statement:
--   The Cusp GL construction uses the root Sum charpoly mem virt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RootPowerSumCharpolyMemVirtualCharactersGL.lean#L213-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RootPowerSumCharpolyMemVirtualCharactersGL.lean#L213-L233

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OneMemClosureInducedCentralByPrimePower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MatrixTraceIffIsCharacterOverSubfieldComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootsCharpolyPowEqMapPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterEsymmRootsCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MultisetPowerSumNewtonIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterBrauerLiftAbelianByPrimePower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharpolyMemVirtualCharactersGL
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
open Polynomial

theorem GlobalTheory.CuspGL.rootSum_charpoly_mem_virt (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (n k : ℕ) :
    (fun x : GL (Fin n) F => _root_.GlobalTheory.CuspGL.rootSum θ k (Matrix.charpoly (x : Matrix (Fin n) (Fin n) F)))
      ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ (GL (Fin n) F) := by sorry
