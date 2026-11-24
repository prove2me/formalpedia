-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_minpoly_map_ringEquiv
-- name    : GroundTheory.PAdicHodge.minpoly_map_ringEquiv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:46:46.013154+00:00
-- url     : https://prove2.me/theorems/8f85bc4a-4453-4ab3-a922-6b0468c13ef3
-- title:
--   PAdic Hodge: minpoly map ring Equiv
-- statement:
--   The PAdic Hodge construction uses the minpoly map ring Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L135-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L135-L147

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

theorem GroundTheory.PAdicHodge.minpoly_map_ringEquiv {F₁ F₂ : Type*} [Field F₁] [Field F₂] [Algebra F₁ Ω] [Algebra F₂ Ω]
    (τ : F₁ ≃+* F₂) (σ : Ω ≃+* Ω) (h : ∀ a, algebraMap F₂ Ω (τ a) = σ (algebraMap F₁ Ω a))
    {y : Ω} (hy : IsIntegral F₁ y) :
    minpoly F₂ (σ y) = (minpoly F₁ y).map (τ : F₁ →+* F₂) := by sorry
