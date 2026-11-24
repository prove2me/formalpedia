-- Prove2me | Theorems.Thm_GlobalTheory_IsHilbertPoly_shift
-- name    : GlobalTheory.IsHilbertPoly.shift
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:21:30.825181+00:00
-- url     : https://prove2.me/theorems/b2715612-7288-43aa-93b2-fe182699d108
-- title:
--   Is Hilbert Poly: shift
-- statement:
--   The Is Hilbert Poly construction uses the shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/XSmulMemWeightedHomogeneousSubmodule.lean#L582-L590
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/XSmulMemWeightedHomogeneousSubmodule.lean#L582-L590

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter
open GlobalTheory
open DirectSum Module GradedHilbert
variable {k : Type*} [Field k] {M' M M'' : Type*} [AddCommGroup M'] [Module k M']
  [AddCommGroup M] [Module k M] [AddCommGroup M''] [Module k M'']

theorem GlobalTheory.IsHilbertPoly.shift {ℳ : ℤ → Submodule k M} {P : ℚ[X]} (hP : IsHilbertPoly ℳ P)
    (d : ℤ) : IsHilbertPoly (fun n => ℳ (n + d)) (P.comp (X + C (d : ℚ))) := by sorry
