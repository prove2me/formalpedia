-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_normTrace_map_of_map_eq
-- name    : GroundTheory.PAdicHodge.normTrace_map_of_map_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:33.171797+00:00
-- url     : https://prove2.me/theorems/ce63edc4-bdf1-4480-ab5e-2d7e2c650ad2
-- title:
--   PAdic Hodge: norm Trace map of map eq
-- statement:
--   The PAdic Hodge construction uses the norm Trace map of map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L157-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L157-L162

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

theorem GroundTheory.PAdicHodge.normTrace_map_of_map_eq {B₀ : Type*} [Field B₀] [Algebra B₀ Ω] [Algebra.IsIntegral B₀ Ω]
    (k : IntermediateField B₀ Ω) (σ : Ω ≃ₐ[B₀] Ω) (hk : k.map (σ : Ω →ₐ[B₀] Ω) = k) (y : Ω) :
    normTrace k (σ y) = σ (normTrace k y) := by sorry
