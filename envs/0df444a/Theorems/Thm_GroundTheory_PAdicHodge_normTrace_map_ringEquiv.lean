-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_normTrace_map_ringEquiv
-- name    : GroundTheory.PAdicHodge.normTrace_map_ringEquiv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:47:27.851129+00:00
-- url     : https://prove2.me/theorems/aa1860e3-d852-48a7-88d0-48260edfecaa
-- title:
--   PAdic Hodge: norm Trace map ring Equiv
-- statement:
--   The PAdic Hodge construction uses the norm Trace map ring Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L149-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L149-L155

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module IntermediateField
noncomputable section
variable {Ω : Type*} [Field Ω]

theorem GroundTheory.PAdicHodge.normTrace_map_ringEquiv {F₁ F₂ : Type*} [Field F₁] [Field F₂] [Algebra F₁ Ω]
    [Algebra F₂ Ω] (τ : F₁ ≃+* F₂) (σ : Ω ≃+* Ω)
    (h : ∀ a, algebraMap F₂ Ω (τ a) = σ (algebraMap F₁ Ω a)) {y : Ω} (hy : IsIntegral F₁ y) :
    normTrace F₂ (σ y) = σ (normTrace F₁ y) := by sorry
