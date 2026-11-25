-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_fixedPoints_closedSubgroup_eq_closure
-- name    : GroundTheory.PAdicHodge.fixedPoints_closedSubgroup_eq_closure
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:29:42.637129+00:00
-- url     : https://prove2.me/theorems/e8048cc2-5c4a-4d3b-ad99-2a779b354217
-- title:
--   PAdic Hodge: fixed Points closed Subgroup eq closure
-- statement:
--   The PAdic Hodge construction uses the fixed Points closed Subgroup eq closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L560-L567
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L560-L567

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
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
open Polynomial
noncomputable section
open UniformSpace Topology
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem GroundTheory.PAdicHodge.fixedPoints_closedSubgroup_eq_closure (H : Subgroup Gal(PadicAlgCl p/K))
    (hH : IsClosed (H : Set Gal(PadicAlgCl p/K))) :
    {x : ℂ_[p] | ∀ σ ∈ H, σ • x = x} =
      closure (((↑) : PadicAlgCl p → ℂ_[p]) ''
        (IntermediateField.fixedField H : Set (PadicAlgCl p))) := by sorry
