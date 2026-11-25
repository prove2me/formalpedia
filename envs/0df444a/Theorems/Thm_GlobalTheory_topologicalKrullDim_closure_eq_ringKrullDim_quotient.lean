-- Prove2me | Theorems.Thm_GlobalTheory_topologicalKrullDim_closure_eq_ringKrullDim_quotient
-- name    : GlobalTheory.topologicalKrullDim_closure_eq_ringKrullDim_quotient
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:42:58.319498+00:00
-- url     : https://prove2.me/theorems/97b46c70-bba4-5a39-96b3-bb6cffd3e9d7
-- title:
--   Global Theory: topological Krull Dim closure eq ring Krull Dim quotient
-- statement:
--   The Global Theory construction uses the topological Krull Dim closure eq ring Krull Dim quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanFinrankMaximalIdealLeNcardOfLeSupSq.lean#L677-L718
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanFinrankMaximalIdealLeNcardOfLeSupSq.lean#L677-L718

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

theorem GlobalTheory.topologicalKrullDim_closure_eq_ringKrullDim_quotient {K : Type u} [Field K]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of K)) [LocallyOfFiniteType p] {B : Type u} [CommRing B]
    (j : Spec (.of B) ⟶ Y) [IsOpenImmersion j] (q : PrimeSpectrum B) :
    topologicalKrullDim (closure {j q} : Set Y) = ringKrullDim (B ⧸ q.asIdeal) := by sorry
