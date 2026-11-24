-- Prove2me | Theorems.Thm_GlobalTheory_dWedge_mem_regForms
-- name    : GlobalTheory.dWedge_mem_regForms
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:14:20.480853+00:00
-- url     : https://prove2.me/theorems/9a5ac69f-e177-457f-bd4a-beaba1eca0bd
-- title:
--   Global Theory: d Wedge mem reg Forms
-- statement:
--   The Global Theory construction uses the d Wedge mem reg Forms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L123-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L123-L125

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
variable (K V F : Type*) [CommRing K] [CommRing V] [CommRing F] [Algebra K V] [Algebra V F]
  [Algebra K F] [IsScalarTower K V F] (p : ℕ)
variable {V p}

theorem GlobalTheory.dWedge_mem_regForms (x : Fin p → V) :
    dWedge K (fun k => algebraMap V F (x k)) ∈ regForms K V F p := by sorry
