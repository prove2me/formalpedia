-- Prove2me | Theorems.Thm_GlobalTheory_EsymmVirt_esymm_eq_of_psum_eq
-- name    : GlobalTheory.EsymmVirt.esymm_eq_of_psum_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:14:24.073331+00:00
-- url     : https://prove2.me/theorems/89d0a6e5-63d5-4129-9e9c-1b07b6072be0
-- title:
--   Esymm Virt: esymm eq of psum eq
-- statement:
--   The Esymm Virt construction uses the esymm eq of psum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EsymmMemVirtualCharactersOfPowerSumEigenvalues.lean#L39-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EsymmMemVirtualCharactersOfPowerSumEigenvalues.lean#L39-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MatrixTraceIffIsCharacterOverSubfieldComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootsCharpolyPowEqMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterEsymmRootsCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MultisetPowerSumNewtonIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EsymmMemVirtualCharactersOfPowerSumEigenvalues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.EsymmVirt

theorem GlobalTheory.EsymmVirt.esymm_eq_of_psum_eq (s t : Multiset ℂ)
    (h : ∀ j : ℕ, 0 < j → (s.map (· ^ j)).sum = (t.map (· ^ j)).sum) (n : ℕ) :
    s.esymm n = t.esymm n := by sorry
