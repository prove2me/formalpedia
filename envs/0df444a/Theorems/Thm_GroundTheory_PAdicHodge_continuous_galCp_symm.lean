-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_continuous_galCp_symm
-- name    : GroundTheory.PAdicHodge.continuous_galCp_symm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:01:16.550793+00:00
-- url     : https://prove2.me/theorems/7735b638-4f3b-465b-89ac-a87c63622620
-- title:
--   PAdic Hodge: continuous gal Cp symm
-- statement:
--   The PAdic Hodge construction uses the continuous gal Cp symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L135-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L135-L136

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

theorem GroundTheory.PAdicHodge.continuous_galCp_symm (σ : Gal(PadicAlgCl p/K)) : Continuous (galCp σ).symm := by sorry
