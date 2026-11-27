-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_eq_galCp_of_continuous
-- name    : GroundTheory.PAdicHodge.eq_galCp_of_continuous
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:09.069193+00:00
-- url     : https://prove2.me/theorems/f9664015-fa0b-5dd2-a036-b5d316a540c4
-- title:
--   PAdic Hodge: eq gal Cp of continuous
-- statement:
--   The PAdic Hodge construction uses the eq gal Cp of continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L138-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean#L138-L141

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

theorem GroundTheory.PAdicHodge.eq_galCp_of_continuous (σ : Gal(PadicAlgCl p/K)) (f : ℂ_[p] → ℂ_[p])
    (hf : Continuous f) (h : ∀ y : PadicAlgCl p, f y = ((σ y : PadicAlgCl p) : ℂ_[p])) :
    f = galCp σ := by sorry
