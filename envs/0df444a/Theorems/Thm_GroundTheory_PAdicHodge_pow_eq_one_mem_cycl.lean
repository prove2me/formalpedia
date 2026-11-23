-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_pow_eq_one_mem_cycl
-- name    : GroundTheory.PAdicHodge.pow_eq_one_mem_cycl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:40.022805+00:00
-- url     : https://prove2.me/theorems/fb1fa2cf-9b40-475d-a715-5b574632089d
-- title:
--   PAdic Hodge: pow eq one mem cycl
-- statement:
--   The PAdic Hodge construction uses the pow eq one mem cycl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicField.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicField.lean#L18-L19

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

theorem GroundTheory.PAdicHodge.pow_eq_one_mem_cycl {n : ℕ} {x : PadicAlgCl p} (hx : x ^ (p ^ n) = 1) : x ∈ cycl p n := by sorry
