-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_exists_eventuallyEq_const_of_meromorphicOrderAt_nonneg
-- name    : GroundTheory.Global.Elliptic.exists_eventuallyEq_const_of_meromorphicOrderAt_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:21.939142+00:00
-- url     : https://prove2.me/theorems/790e9395-b39b-4c5e-993c-89beb372fd47
-- title:
--   Elliptic: exists eventually Eq const of meromorphic Order At nonneg
-- statement:
--   The Elliptic construction uses the exists eventually Eq const of meromorphic Order At nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticConstant.lean#L78-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticConstant.lean#L78-L84

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {E : Type*} [NormedAddCommGroup E]
variable [NormedSpace ℂ E]
variable {L : PeriodPair}
variable (L)

theorem GroundTheory.Global.Elliptic.exists_eventuallyEq_const_of_meromorphicOrderAt_nonneg [CompleteSpace E] {f : ℂ → E} (hf : Meromorphic f)
    (hp : IsPeriodic L f) (ho : ∀ z, 0 ≤ meromorphicOrderAt f z) :
    ∃ c : E, f =ᶠ[codiscrete ℂ] fun _ ↦ c := by sorry
