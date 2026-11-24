-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_mem_padicComplexInt_iff
-- name    : GroundTheory.PAdicHodge.mem_padicComplexInt_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:55:09.9698+00:00
-- url     : https://prove2.me/theorems/b9f954c1-551a-4d0b-ab5c-145912ac3d7d
-- title:
--   PAdic Hodge: mem padic Complex Int iff
-- statement:
--   The PAdic Hodge construction uses the mem padic Complex Int iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L154-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L154-L158

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

theorem GroundTheory.PAdicHodge.mem_padicComplexInt_iff (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by sorry
