-- Prove2me | Theorems.Thm_GlobalTheory_length_quotient_eq_addVal_det_basis
-- name    : GlobalTheory.length_quotient_eq_addVal_det_basis
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:49:14.207944+00:00
-- url     : https://prove2.me/theorems/abb2909b-6b83-4985-81c3-e82ad2d4524a
-- title:
--   Global Theory: length quotient eq add Val det basis
-- statement:
--   The Global Theory construction uses the length quotient eq add Val det basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableSpanSpanOfDetNeZero.lean#L128-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableSpanSpanOfDetNeZero.lean#L128-L135

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
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.length_quotient_eq_addVal_det_basis (b : Basis ι R M) (N : Submodule R M)
    (c : Basis ι R N) : Module.length R (M ⧸ N) = addVal R (b.det fun i => (c i : M)) := by sorry
