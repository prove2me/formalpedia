-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_galCp_mul
-- name    : GroundTheory.PAdicHodge.galCp_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:28.643591+00:00
-- url     : https://prove2.me/theorems/53b619d7-c1d4-4426-bb57-42333e362736
-- title:
--   PAdic Hodge: gal Cp mul
-- statement:
--   The PAdic Hodge construction uses the gal Cp mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L148-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L148-L149

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

theorem GroundTheory.PAdicHodge.galCp_mul (σ τ : Gal(PadicAlgCl p/K)) : galCp (σ * τ) = (galCp τ).trans (galCp σ) := by sorry
