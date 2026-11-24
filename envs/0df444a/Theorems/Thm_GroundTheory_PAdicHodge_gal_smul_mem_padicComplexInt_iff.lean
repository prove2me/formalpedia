-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_gal_smul_mem_padicComplexInt_iff
-- name    : GroundTheory.PAdicHodge.gal_smul_mem_padicComplexInt_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:47:02.647381+00:00
-- url     : https://prove2.me/theorems/d05e9e32-a19f-4197-b08e-a8d64f086aa8
-- title:
--   PAdic Hodge: gal smul mem padic Complex Int iff
-- statement:
--   The PAdic Hodge construction uses the gal smul mem padic Complex Int iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L160-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L160-L162

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

theorem GroundTheory.PAdicHodge.gal_smul_mem_padicComplexInt_iff (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) :
    σ • x ∈ 𝓞_ℂ_[p] ↔ x ∈ 𝓞_ℂ_[p] := by sorry
