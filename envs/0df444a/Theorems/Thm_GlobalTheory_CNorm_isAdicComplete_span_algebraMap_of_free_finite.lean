-- Prove2me | Theorems.Thm_GlobalTheory_CNorm_isAdicComplete_span_algebraMap_of_free_finite
-- name    : GlobalTheory.CNorm.isAdicComplete_span_algebraMap_of_free_finite
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:06:15.95535+00:00
-- url     : https://prove2.me/theorems/7d299eea-9191-4652-8154-6371f7d73a8b
-- title:
--   CNorm: is Adic Complete span algebra Map of free finite
-- statement:
--   The CNorm construction uses the is Adic Complete span algebra Map of free finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsAdicCompleteSpanAlgebraMapOfFreeFinite.lean#L51-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsAdicCompleteSpanAlgebraMapOfFreeFinite.lean#L51-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteSpanAlgebraMapOfFreeFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm

theorem GlobalTheory.CNorm.isAdicComplete_span_algebraMap_of_free_finite :
    ∀ (R O : Type) [CommRing R] [CommRing O] [Algebra R O] [Module.Free R O] [Module.Finite R O]
      (t : R), IsAdicComplete (Ideal.span {t}) R →
        IsAdicComplete (Ideal.span {algebraMap R O t}) O := by sorry
