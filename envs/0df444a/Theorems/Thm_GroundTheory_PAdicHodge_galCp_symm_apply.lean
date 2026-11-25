-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_galCp_symm_apply
-- name    : GroundTheory.PAdicHodge.galCp_symm_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:20.087803+00:00
-- url     : https://prove2.me/theorems/16f684bb-6c73-4b46-b08b-18b6cd833d0a
-- title:
--   PAdic Hodge: gal Cp symm apply
-- statement:
--   The PAdic Hodge construction uses the gal Cp symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L123-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L123-L124

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
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
open UniformSpace Topology Filter
noncomputable section
variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem GroundTheory.PAdicHodge.galCp_symm_apply (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) :
    (galCp σ).symm x = σ⁻¹ • x := by sorry
