-- Prove2me | Theorems.Thm_GlobalTheory_isZero_homology_extendScalars_iff
-- name    : GlobalTheory.isZero_homology_extendScalars_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:01:30.229804+00:00
-- url     : https://prove2.me/theorems/e8ac1ee7-e542-4562-9895-d51d9d6311ca
-- title:
--   Global Theory: is Zero homology extend Scalars iff
-- statement:
--   The Global Theory construction uses the is Zero homology extend Scalars iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndKerBaseChangeOfForallResidueField.lean#L249-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndKerBaseChangeOfForallResidueField.lean#L249-L259

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Function
open GlobalTheory
open CategoryTheory Category Limits
universe u w
variable {R : Type u} [CommRing R] {ι : Type*} {c : ComplexShape ι}

theorem GlobalTheory.isZero_homology_extendScalars_iff (S : Type w) [CommRing S] [inst : Algebra R S]
    (K : HomologicalComplex (ModuleCat.{u} R) c) {p q r : ι} (hp : c.prev q = p)
    (hr : c.next q = r) :
    IsZero ((((ModuleCat.extendScalars.{u, w, u} (algebraMap R S)).mapHomologicalComplex c).obj
        K).homology q) ↔
      Exact ((K.d p q).hom.lTensor S) ((K.d q r).hom.lTensor S) := by sorry
