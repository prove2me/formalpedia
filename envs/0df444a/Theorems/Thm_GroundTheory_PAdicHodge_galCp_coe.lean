-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_galCp_coe
-- name    : GroundTheory.PAdicHodge.galCp_coe
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:20.573806+00:00
-- url     : https://prove2.me/theorems/e39c1e4c-a487-44dd-aaaf-41e4dc0fb952
-- title:
--   PAdic Hodge: gal Cp coe
-- statement:
--   The PAdic Hodge construction uses the gal Cp coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L119-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L119-L121

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

theorem GroundTheory.PAdicHodge.galCp_coe (σ : Gal(PadicAlgCl p/K)) (y : PadicAlgCl p) :
    galCp σ (y : ℂ_[p]) = ((σ y : PadicAlgCl p) : ℂ_[p]) := by sorry
