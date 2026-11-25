-- Prove2me | Theorems.Thm_GlobalTheory_ringKrullDim_localizationAway_eq
-- name    : GlobalTheory.ringKrullDim_localizationAway_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:43:39.860474+00:00
-- url     : https://prove2.me/theorems/e989d2fe-1d7b-4c4c-b1a0-8dee50ad06ec
-- title:
--   Global Theory: ring Krull Dim localization Away eq
-- statement:
--   The Global Theory construction uses the ring Krull Dim localization Away eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanFinrankMaximalIdealLeNcardOfLeSupSq.lean#L664-L675
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanFinrankMaximalIdealLeNcardOfLeSupSq.lean#L664-L675

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

theorem GlobalTheory.ringKrullDim_localizationAway_eq (K : Type u) [Field K] {C : Type u} [CommRing C]
    [IsDomain C] [Algebra K C] [Algebra.FiniteType K C] {g : C} (hg : g ≠ 0) :
    ringKrullDim (Localization.Away g) = ringKrullDim C := by sorry
