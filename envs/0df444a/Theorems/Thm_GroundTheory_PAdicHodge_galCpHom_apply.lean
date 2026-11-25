-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_galCpHom_apply
-- name    : GroundTheory.PAdicHodge.galCpHom_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:24.792098+00:00
-- url     : https://prove2.me/theorems/9ecdb922-54f1-4e38-90f9-22ea63e1d09d
-- title:
--   PAdic Hodge: gal Cp Hom apply
-- statement:
--   The PAdic Hodge construction uses the gal Cp Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L146-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L146-L146

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

theorem GroundTheory.PAdicHodge.galCpHom_apply (σ : Gal(PadicAlgCl p/K)) : galCpHom σ = galCp σ := by sorry
