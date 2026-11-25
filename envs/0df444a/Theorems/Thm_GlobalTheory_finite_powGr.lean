-- Prove2me | Theorems.Thm_GlobalTheory_finite_powGr
-- name    : GlobalTheory.finite_powGr
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:46:12.317539+00:00
-- url     : https://prove2.me/theorems/fbecb42a-bfaa-429f-9f50-f98f66204804
-- title:
--   Global Theory: finite pow Gr
-- statement:
--   The Global Theory construction uses the finite pow Gr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L498-L504
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L498-L504

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

theorem GlobalTheory.finite_powGr {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] (f : ι → R)
    (a : ℕ) :
    Module.Finite (R ⧸ Ideal.span (Set.range f)) (powGr (Ideal.span (Set.range f)) M a) := by sorry
