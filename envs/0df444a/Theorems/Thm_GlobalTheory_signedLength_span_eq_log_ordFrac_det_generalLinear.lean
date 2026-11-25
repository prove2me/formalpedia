-- Prove2me | Theorems.Thm_GlobalTheory_signedLength_span_eq_log_ordFrac_det_generalLinear
-- name    : GlobalTheory.signedLength_span_eq_log_ordFrac_det_generalLinear
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:01:24.359345+00:00
-- url     : https://prove2.me/theorems/54c77cca-7e4a-49b2-88db-fdb8c20ea681
-- title:
--   Global Theory: signed Length span eq log ord Frac det general Linear
-- statement:
--   The Global Theory construction uses the signed Length span eq log ord Frac det general Linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableSpanSpanOfDetNeZero.lean#L253-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableSpanSpanOfDetNeZero.lean#L253-L259

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsDualNeZeroCompEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthQuotientSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthSelfEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsLinearEquivMapLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthOfCommonLower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RelLengthSpanEqAddValDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCokerOfNotInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthSpanEqOrdFracDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RelLengthSpanMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthEqLogOrdFracDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthMapEqLogOrdFracDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing
open GlobalTheory
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.signedLength_span_eq_log_ordFrac_det_generalLinear {a b : ι → V}
    (ha : LinearIndependent K a) (g : GL ι K) (hb : ∀ j, b j = ∑ i, g i j • a i) :
    LengthCommensurable (Submodule.span R (Set.range a)) (Submodule.span R (Set.range b)) ∧
      signedLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range b)) =
        WithZero.log (Ring.ordFrac R (g : Matrix ι ι K).det) := by sorry
