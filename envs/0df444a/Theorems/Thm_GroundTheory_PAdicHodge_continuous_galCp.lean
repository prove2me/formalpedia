-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_continuous_galCp
-- name    : GroundTheory.PAdicHodge.continuous_galCp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:46:53.182964+00:00
-- url     : https://prove2.me/theorems/66cddacc-43ba-4209-8807-10446893582d
-- title:
--   PAdic Hodge: continuous gal Cp
-- statement:
--   The PAdic Hodge construction uses the continuous gal Cp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L132-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L132-L133

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

theorem GroundTheory.PAdicHodge.continuous_galCp (σ : Gal(PadicAlgCl p/K)) : Continuous (galCp σ) := by sorry
