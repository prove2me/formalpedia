-- Prove2me | Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_powGrBasis_apply
-- name    : GlobalTheory.IsQuasiRegularSeq.powGrBasis_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:10:53.376839+00:00
-- url     : https://prove2.me/theorems/8bee95c8-093a-5718-b2e2-9609af590cd3
-- title:
--   Is Quasi Regular Seq: pow Gr Basis apply
-- statement:
--   The Is Quasi Regular Seq construction uses the pow Gr Basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L469-L489
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L469-L489

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]

theorem GlobalTheory.IsQuasiRegularSeq.powGrBasis_apply {f : ι → R} (h : IsQuasiRegularSeq R f) (a : ℕ)
    (α : MonoDeg ι a) : h.powGrBasis a α = powGr.mk _ R a
      ⟨monoVal f α.1, by simpa using monoVal_mem_pow f α⟩ := by sorry
