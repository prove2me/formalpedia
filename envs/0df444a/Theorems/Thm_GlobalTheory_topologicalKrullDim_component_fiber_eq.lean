-- Prove2me | Theorems.Thm_GlobalTheory_topologicalKrullDim_component_fiber_eq
-- name    : GlobalTheory.topologicalKrullDim_component_fiber_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:51:25.468557+00:00
-- url     : https://prove2.me/theorems/a5d960a1-11dd-4dd2-8781-ac314a481de1
-- title:
--   Global Theory: topological Krull Dim component fiber eq
-- statement:
--   The Global Theory construction uses the topological Krull Dim component fiber eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RingKrullDimQuotientEqOfMemMinimalPrimes.lean#L553-L558
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RingKrullDimQuotientEqOfMemMinimalPrimes.lean#L553-L558

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing
open GlobalTheory
universe u
open AlgebraicGeometry CategoryTheory Topology Limits
variable {O : Type u} [CommRing O] [IsDomain O]
  {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ Spec (.of O)) [LocallyOfFiniteType f] [Flat f]
variable [IsDiscreteValuationRing O]

theorem GlobalTheory.topologicalKrullDim_component_fiber_eq {Z : Set (f.fiber (closedPoint O))}
    (hZ : Z ∈ irreducibleComponents (f.fiber (closedPoint O))) :
    topologicalKrullDim Z = topologicalKrullDim (f.fiber (genericPoint (Spec (.of O)))) := by sorry
