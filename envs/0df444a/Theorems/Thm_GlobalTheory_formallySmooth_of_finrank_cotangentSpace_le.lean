-- Prove2me | Theorems.Thm_GlobalTheory_formallySmooth_of_finrank_cotangentSpace_le
-- name    : GlobalTheory.formallySmooth_of_finrank_cotangentSpace_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:43:08.760751+00:00
-- url     : https://prove2.me/theorems/eb8bb366-e06f-5068-9506-0b5f143f2f74
-- title:
--   Global Theory: formally Smooth of finrank cotangent Space le
-- statement:
--   The Global Theory construction uses the formally Smooth of finrank cotangent Space le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanFinrankMaximalIdealLeNcardOfLeSupSq.lean#L250-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanFinrankMaximalIdealLeNcardOfLeSupSq.lean#L250-L257

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

theorem GlobalTheory.formallySmooth_of_finrank_cotangentSpace_le (k S : Type*) [Field k] [PerfectField k]
    [CommRing S] [IsLocalRing S] [Algebra k S] [Algebra.EssFiniteType k S] {d : ℕ}
    (h₁ : (d : WithBot ℕ∞) ≤ ringKrullDim S)
    (h₂ : Module.finrank (ResidueField S) (CotangentSpace S) ≤ d) :
    Algebra.FormallySmooth k S := by sorry
