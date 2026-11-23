-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_cycl_map
-- name    : GroundTheory.PAdicHodge.cycl_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:22.419706+00:00
-- url     : https://prove2.me/theorems/7543d180-01d4-43d1-85cd-0e715ff0cc98
-- title:
--   PAdic Hodge: cycl map
-- statement:
--   The PAdic Hodge construction uses the cycl map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicField.lean#L55-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicField.lean#L55-L67

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

theorem GroundTheory.PAdicHodge.cycl_map (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (n : ℕ) :
    (cycl p n).map (σ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p) = cycl p n := by sorry
