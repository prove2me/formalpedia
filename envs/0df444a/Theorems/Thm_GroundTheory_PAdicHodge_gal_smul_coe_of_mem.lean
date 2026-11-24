-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_gal_smul_coe_of_mem
-- name    : GroundTheory.PAdicHodge.gal_smul_coe_of_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:41.149861+00:00
-- url     : https://prove2.me/theorems/891baf23-83f6-4f42-bb77-a42d62b4dee4
-- title:
--   PAdic Hodge: gal smul coe of mem
-- statement:
--   The PAdic Hodge construction uses the gal smul coe of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L98-L101

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

theorem GroundTheory.PAdicHodge.gal_smul_coe_of_mem (σ : Gal(PadicAlgCl p/K)) (k : K) :
    σ • ((k : PadicAlgCl p) : ℂ_[p]) = ((k : PadicAlgCl p) : ℂ_[p]) := by sorry
