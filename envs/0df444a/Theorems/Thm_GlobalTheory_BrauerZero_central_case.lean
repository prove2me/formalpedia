-- Prove2me | Theorems.Thm_GlobalTheory_BrauerZero_central_case
-- name    : GlobalTheory.BrauerZero.central_case
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:59:58.655801+00:00
-- url     : https://prove2.me/theorems/f2ae43bb-56cb-4a7a-9ddc-b15e83b93c0c
-- title:
--   Brauer Zero: central case
-- statement:
--   The Brauer Zero construction uses the central case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BrauerDegreeZero.lean#L100-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BrauerDegreeZero.lean#L100-L153

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__BrauerDegreeZero_fefd58e19a2fa426
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldInductionIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MemVirtualCharactersIffSubCharacters
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleCharacterLinearOrInducedAbelianByPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IndMulClassFunEqIndMulRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OneMemClosureInducedCentralByPrimePower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndApplyOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedClassFunctionFromSubgroupTransStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedClassFunctionMemInducedDegreeOneCharDiffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedOneSubIndexMemDegreeOneCharacterDiffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLtCommutatorMemOfNeTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BrauerDegreeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.BI
open GlobalTheory GlobalTheory.BrauerZero

theorem GlobalTheory.BrauerZero.central_case (G : Type) [Group G] [Finite G]
    (hG : ∃ l : ℕ, l.Prime ∧ ∀ y : G, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center G)
    (IH : ∀ T : Subgroup G, T ≠ ⊤ → ∀ f ∈ Virt ℂ ℂ T, f 1 = 0 → f ∈ D0 T) :
    ∀ f ∈ Virt ℂ ℂ G, f 1 = 0 → f ∈ D0 G := by sorry
