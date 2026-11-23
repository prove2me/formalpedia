-- Prove2me | Theorems.Thm_GlobalTheory_ker_includeRight_fiber
-- name    : GlobalTheory.ker_includeRight_fiber
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:22.231611+00:00
-- url     : https://prove2.me/theorems/16e2baf9-4787-4d8d-84c9-92fb21a84b9d
-- title:
--   Global Theory: ker include Right fiber
-- statement:
--   The Global Theory construction uses the ker include Right fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L250-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L250-L259

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {M : Type*} [AddCommGroup M] [Module A M]
variable [Module B M] [IsScalarTower A B M] [Module.Flat A M]
variable [Module.Flat A B]

theorem GlobalTheory.ker_includeRight_fiber (p : Ideal A) [p.IsPrime] :
    RingHom.ker (Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B) =
      p.map (algebraMap A B) := by sorry
