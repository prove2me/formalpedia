-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_gal_smul_algebraMap
-- name    : GroundTheory.PAdicHodge.gal_smul_algebraMap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:30:10.397384+00:00
-- url     : https://prove2.me/theorems/93f49b24-94f6-4669-9b45-724e17f1fc42
-- title:
--   PAdic Hodge: gal smul algebra Map
-- statement:
--   The PAdic Hodge construction uses the gal smul algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L103-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L103-L108

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

theorem GroundTheory.PAdicHodge.gal_smul_algebraMap (σ : Gal(PadicAlgCl p/K)) (q : ℚ_[p]) :
    σ • algebraMap ℚ_[p] ℂ_[p] q = algebraMap ℚ_[p] ℂ_[p] q := by sorry
