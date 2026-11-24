-- Prove2me | Theorems.Thm_GlobalTheory_SimMult_exists_norm_finiteField
-- name    : GlobalTheory.SimMult.exists_norm_finiteField
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:13:23.974109+00:00
-- url     : https://prove2.me/theorems/fc6b3243-677f-40d2-86c3-61e525865487
-- title:
--   Sim Mult: exists norm finite Field
-- statement:
--   The Sim Mult construction uses the exists norm finite Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSimTrivialOfMult.lean#L56-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSimTrivialOfMult.lean#L56-L96

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSimTrivialOfMult
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SimMult

theorem GlobalTheory.SimMult.exists_norm_finiteField {k : Type*} [Field k] [Finite k] (σ : k →+* k)
    (hσ : ∀ x, σ (σ x) = x) (hne : ∃ t, σ t ≠ t) (ν : ℤ) (hν : (ν : k) ≠ 0) :
    ∃ c, c * σ c = ν := by sorry
