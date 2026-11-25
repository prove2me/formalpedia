-- Prove2me | Theorems.Thm_GlobalTheory_closure_mem_irreducibleComponents_of_mem_minimalPrimes
-- name    : GlobalTheory.closure_mem_irreducibleComponents_of_mem_minimalPrimes
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:43:42.667813+00:00
-- url     : https://prove2.me/theorems/e02c9569-a601-49d7-8618-b247b72671ef
-- title:
--   Global Theory: closure mem irreducible Components of mem minimal Primes
-- statement:
--   The Global Theory construction uses the closure mem irreducible Components of mem minimal Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanFinrankMaximalIdealLeNcardOfLeSupSq.lean#L720-L731
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanFinrankMaximalIdealLeNcardOfLeSupSq.lean#L720-L731

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

theorem GlobalTheory.closure_mem_irreducibleComponents_of_mem_minimalPrimes {Y : Scheme.{u}} {B : Type u}
    [CommRing B] (j : Spec (.of B) ⟶ Y) [IsOpenImmersion j] (q : PrimeSpectrum B)
    (hq : q.asIdeal ∈ minimalPrimes B) : closure {j q} ∈ irreducibleComponents Y := by sorry
