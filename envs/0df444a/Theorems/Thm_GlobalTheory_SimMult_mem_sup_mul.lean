-- Prove2me | Theorems.Thm_GlobalTheory_SimMult_mem_sup_mul
-- name    : GlobalTheory.SimMult.mem_sup_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:14:24.305951+00:00
-- url     : https://prove2.me/theorems/2383b822-5ce2-44fa-bf79-7ae0bdfea8c5
-- title:
--   Sim Mult: mem sup mul
-- statement:
--   The Sim Mult construction uses the mem sup mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSimTrivialOfMult.lean#L208-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSimTrivialOfMult.lean#L208-L216

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
variable {O : Type*} [CommRing O] (σ : O →+* O)

theorem GlobalTheory.SimMult.mem_sup_mul (J : Ideal O) {a b u v x : O} (h : u * a + v * b = 1)
    (ha : x ∈ J ⊔ Ideal.span {a}) (hb : x ∈ J ⊔ Ideal.span {b}) : x ∈ J ⊔ Ideal.span {a * b} := by sorry
