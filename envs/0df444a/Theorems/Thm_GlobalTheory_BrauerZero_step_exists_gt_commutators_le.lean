-- Prove2me | Theorems.Thm_GlobalTheory_BrauerZero_step_exists_gt_commutators_le
-- name    : GlobalTheory.BrauerZero.step_exists_gt_commutators_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:59:33.30045+00:00
-- url     : https://prove2.me/theorems/6b693ebe-2354-4d1a-a7c5-91c886429f34
-- title:
--   Brauer Zero: step exists gt commutators le
-- statement:
--   The Brauer Zero construction uses the step exists gt commutators le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BrauerDegreeZero.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BrauerDegreeZero.lean#L36-L38

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

theorem GlobalTheory.BrauerZero.step_exists_gt_commutators_le {G : Type} [Group G] [Finite G] [Group.IsNilpotent G] (K : Subgroup G)
    (hK : K ≠ ⊤) : ∃ A : Subgroup G, K < A ∧ ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ K := by sorry
