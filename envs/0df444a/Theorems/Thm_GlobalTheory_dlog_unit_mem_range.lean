-- Prove2me | Theorems.Thm_GlobalTheory_dlog_unit_mem_range
-- name    : GlobalTheory.dlog_unit_mem_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:12:42.690251+00:00
-- url     : https://prove2.me/theorems/6bd66cd9-dad5-4848-8db6-39300f2bd320
-- title:
--   Global Theory: dlog unit mem range
-- statement:
--   The Global Theory construction uses the dlog unit mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L168-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L168-L172

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (K : Type*) {F : Type*} [CommRing K] [Field F] [Algebra K F] {p : ℕ}
variable {V : Type*} [CommRing V] [Algebra K V] [Algebra V F] [IsScalarTower K V F]

theorem GlobalTheory.dlog_unit_mem_range (u : Vˣ) :
    (algebraMap V F u)⁻¹ • D K F (algebraMap V F u)
      ∈ LinearMap.range (KaehlerDifferential.map K K V F) := by sorry
