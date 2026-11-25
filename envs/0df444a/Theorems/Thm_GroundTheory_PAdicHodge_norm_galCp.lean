-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_galCp
-- name    : GroundTheory.PAdicHodge.norm_galCp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:47:25.578473+00:00
-- url     : https://prove2.me/theorems/5ef24aa4-66ac-4b28-8e76-188effa24599
-- title:
--   PAdic Hodge: norm gal Cp
-- statement:
--   The PAdic Hodge construction uses the norm gal Cp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L126-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L126-L127

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

theorem GroundTheory.PAdicHodge.norm_galCp (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) : ‖galCp σ x‖ = ‖x‖ := by sorry
