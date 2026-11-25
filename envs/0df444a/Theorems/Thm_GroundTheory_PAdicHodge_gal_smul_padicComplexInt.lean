-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_gal_smul_padicComplexInt
-- name    : GroundTheory.PAdicHodge.gal_smul_padicComplexInt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:46.095873+00:00
-- url     : https://prove2.me/theorems/e7ca7c5d-b697-4f21-8c6d-901990b0a2eb
-- title:
--   PAdic Hodge: gal smul padic Complex Int
-- statement:
--   The PAdic Hodge construction uses the gal smul padic Complex Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L164-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L164-L170

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

theorem GroundTheory.PAdicHodge.gal_smul_padicComplexInt (σ : Gal(PadicAlgCl p/K)) :
    (fun x : ℂ_[p] => σ • x) '' (𝓞_ℂ_[p] : Set ℂ_[p]) = 𝓞_ℂ_[p] := by sorry
