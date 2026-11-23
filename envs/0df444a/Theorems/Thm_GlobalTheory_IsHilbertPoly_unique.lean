-- Prove2me | Theorems.Thm_GlobalTheory_IsHilbertPoly_unique
-- name    : GlobalTheory.IsHilbertPoly.unique
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:51.795807+00:00
-- url     : https://prove2.me/theorems/294604a7-07be-4fd7-abb3-095e01eb75d9
-- title:
--   Is Hilbert Poly: unique
-- statement:
--   The Is Hilbert Poly construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/XSmulMemWeightedHomogeneousSubmodule.lean#L576-L580
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/XSmulMemWeightedHomogeneousSubmodule.lean#L576-L580

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

theorem GlobalTheory.IsHilbertPoly.unique {ℳ : ℤ → Submodule k M} {P Q : ℚ[X]} (hP : IsHilbertPoly ℳ P)
    (hQ : IsHilbertPoly ℳ Q) : P = Q := by sorry
