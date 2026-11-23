-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_map_mem_cycl
-- name    : GroundTheory.PAdicHodge.map_mem_cycl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:30.240804+00:00
-- url     : https://prove2.me/theorems/37133e14-316b-4917-a3d3-5c8fca79e711
-- title:
--   PAdic Hodge: map mem cycl
-- statement:
--   The PAdic Hodge construction uses the map mem cycl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicField.lean#L69-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicField.lean#L69-L72

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
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
open IntermediateField Polynomial
noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {p}

theorem GroundTheory.PAdicHodge.map_mem_cycl (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {n : ℕ} {x : PadicAlgCl p}
    (hx : x ∈ cycl p n) : σ x ∈ cycl p n := by sorry
