-- Prove2me | Theorems.Thm_GlobalTheory_jacForm_eq_jetWedge
-- name    : GlobalTheory.jacForm_eq_jetWedge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:34.923491+00:00
-- url     : https://prove2.me/theorems/16be7f07-9ad5-4dc3-9f17-4175eb7176b4
-- title:
--   Global Theory: jac Form eq jet Wedge
-- statement:
--   The Global Theory construction uses the jac Form eq jet Wedge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L139-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L139-L141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators
variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [AddCommGroup N] [Module A N] {D : ℕ}
variable (d : Derivation R A M) (ω : M [⋀^Fin D]→ₗ[A] N)

theorem GlobalTheory.jacForm_eq_jetWedge (f : Fin (D + 1) → A) :
    jacForm d ω f = jetWedge ω (fun i => (f i, d (f i))) := by sorry
