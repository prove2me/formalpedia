-- Prove2me | Theorems.Thm_GlobalTheory_ker_map_comp_killVars
-- name    : GlobalTheory.ker_map_comp_killVars
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:06:52.798273+00:00
-- url     : https://prove2.me/theorems/c0ddebed-8bb1-492a-ab3a-e93d970fc849
-- title:
--   Global Theory: ker map comp kill Vars
-- statement:
--   The Global Theory construction uses the ker map comp kill Vars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L81-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L81-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial RingTheory.Sequence
noncomputable section
open GlobalTheory
variable {R : Type*} [CommRing R] {σ : Type*}

theorem GlobalTheory.ker_map_comp_killVars (S : Set σ) (I : Ideal R) :
    RingHom.ker ((MvPolynomial.map (Ideal.Quotient.mk I)).comp (killVars R S).toRingHom) =
      I.map (C : R →+* MvPolynomial σ R) ⊔ Ideal.span (X '' S) := by sorry
