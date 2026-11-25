-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_isometry_galCp
-- name    : GroundTheory.PAdicHodge.isometry_galCp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:47:00.738677+00:00
-- url     : https://prove2.me/theorems/efaaa2ea-4c6d-4654-8adc-a77e906252bb
-- title:
--   PAdic Hodge: isometry gal Cp
-- statement:
--   The PAdic Hodge construction uses the isometry gal Cp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L129-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L129-L130

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

theorem GroundTheory.PAdicHodge.isometry_galCp (σ : Gal(PadicAlgCl p/K)) : Isometry (galCp σ) := by sorry
