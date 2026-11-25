-- Prove2me | Theorems.Thm_GlobalTheory_T_esymm_mem_virtualCharacters_of_powerSum_eigenvalues
-- name    : GlobalTheory.T.esymm_mem_virtualCharacters_of_powerSum_eigenvalues
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:52:47.468517+00:00
-- url     : https://prove2.me/theorems/561d6d42-5864-4e0f-b884-e8e89e094be9
-- title:
--   T: esymm mem virtual Characters of power Sum eigenvalues
-- statement:
--   The T construction uses the esymm mem virtual Characters of power Sum eigenvalues property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EsymmMemVirtualCharactersOfPowerSumEigenvaluesStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EsymmMemVirtualCharactersOfPowerSumEigenvaluesStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EsymmMemVirtualCharactersOfPowerSumEigenvalues
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EsymmMemVirtualCharactersOfPowerSumEigenvaluesStatement
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

theorem GlobalTheory.T.esymm_mem_virtualCharacters_of_powerSum_eigenvalues : ∀ (G : Type) [Group G] [Finite G] (φ : G → ℂ) (x : G → Multiset ℂ), φ ∈ Virt ℂ ℂ G → (∀ (g : G) (j : ℕ), 0 < j → φ (g ^ j) = ((x g).map (· ^ j)).sum) → ∀ s : ℕ, (fun g => (x g).esymm s) ∈ Virt ℂ ℂ G := by sorry
