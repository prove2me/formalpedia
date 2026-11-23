-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_cycl_eq_adjoin
-- name    : GroundTheory.PAdicHodge.cycl_eq_adjoin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:25.157186+00:00
-- url     : https://prove2.me/theorems/643600cb-0b49-41d7-8101-fc255be5c8ef
-- title:
--   PAdic Hodge: cycl eq adjoin
-- statement:
--   The PAdic Hodge construction uses the cycl eq adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicField.lean#L45-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicField.lean#L45-L53

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

theorem GroundTheory.PAdicHodge.cycl_eq_adjoin {n : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    cycl p n = ℚ_[p]⟮ζ⟯ := by sorry
