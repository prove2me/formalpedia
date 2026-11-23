-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_isPrimitiveRoot
-- name    : GroundTheory.PAdicHodge.exists_isPrimitiveRoot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:39.91907+00:00
-- url     : https://prove2.me/theorems/cd5ba257-b0cb-41ff-b379-37af18bdb55b
-- title:
--   PAdic Hodge: exists is Primitive Root
-- statement:
--   The PAdic Hodge construction uses the exists is Primitive Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicField.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicField.lean#L37-L43

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

theorem GroundTheory.PAdicHodge.exists_isPrimitiveRoot (n : ℕ) : ∃ ζ : PadicAlgCl p, IsPrimitiveRoot ζ (p ^ n) := by sorry
