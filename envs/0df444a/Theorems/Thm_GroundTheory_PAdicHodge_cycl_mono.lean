-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_cycl_mono
-- name    : GroundTheory.PAdicHodge.cycl_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:16.984965+00:00
-- url     : https://prove2.me/theorems/183ec826-2e7f-4a01-ac3d-987817e66c2c
-- title:
--   PAdic Hodge: cycl mono
-- statement:
--   The PAdic Hodge construction uses the cycl mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicField.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicField.lean#L21-L25

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

theorem GroundTheory.PAdicHodge.cycl_mono : Monotone (cycl p) := by sorry
