-- Prove2me | Theorems.Thm_GlobalTheory_formMap_dWedge
-- name    : GlobalTheory.formMap_dWedge
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:47:53.314432+00:00
-- url     : https://prove2.me/theorems/59cb1254-fa2a-415e-87d7-519eae3f301b
-- title:
--   Global Theory: form Map d Wedge
-- statement:
--   The Global Theory construction uses the form Map d Wedge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L113-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L113-L115

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

theorem GlobalTheory.formMap_dWedge (x : Fin p → V) :
    formMap K V F p (dWedge K x) = dWedge K (fun k => algebraMap V F (x k)) := by sorry
