-- Prove2me | Theorems.Thm_GlobalTheory_PerfectCompletion_complete
-- name    : GlobalTheory.PerfectCompletion.complete
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:30.985475+00:00
-- url     : https://prove2.me/theorems/38bf4f04-47dd-4d73-94eb-b5422db940db
-- title:
--   Perfect Completion: complete
-- statement:
--   The Perfect Completion construction uses the complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionPrincipalPerfect.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionPrincipalPerfect.lean#L21-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionPrincipalPerfect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PerfectCompletion
variable {V : Type} [CommRing V] (x : V)

theorem GlobalTheory.PerfectCompletion.complete :
    IsAdicComplete (Ideal.span {algebraMap V (AdicCompletion (Ideal.span {x}) V) x})
      (AdicCompletion (Ideal.span {x}) V) := by sorry
