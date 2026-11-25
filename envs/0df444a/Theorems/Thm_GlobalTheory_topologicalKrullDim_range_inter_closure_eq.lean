-- Prove2me | Theorems.Thm_GlobalTheory_topologicalKrullDim_range_inter_closure_eq
-- name    : GlobalTheory.topologicalKrullDim_range_inter_closure_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:44:27.123841+00:00
-- url     : https://prove2.me/theorems/958efce5-166d-498f-b1d1-ec521b1e631b
-- title:
--   Global Theory: topological Krull Dim range inter closure eq
-- statement:
--   The Global Theory construction uses the topological Krull Dim range inter closure eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanFinrankMaximalIdealLeNcardOfLeSupSq.lean#L649-L662
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanFinrankMaximalIdealLeNcardOfLeSupSq.lean#L649-L662

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
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
open AlgebraicGeometry CategoryTheory Topology

theorem GlobalTheory.topologicalKrullDim_range_inter_closure_eq {Y : Scheme.{u}} {B : Type u} [CommRing B]
    (j : Spec (.of B) ⟶ Y) [IsOpenImmersion j] (q : PrimeSpectrum B) :
    topologicalKrullDim (Set.range j ∩ closure {j q} : Set Y) = ringKrullDim (B ⧸ q.asIdeal) := by sorry
