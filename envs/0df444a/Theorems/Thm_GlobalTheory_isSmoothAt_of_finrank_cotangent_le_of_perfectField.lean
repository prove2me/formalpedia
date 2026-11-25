-- Prove2me | Theorems.Thm_GlobalTheory_isSmoothAt_of_finrank_cotangent_le_of_perfectField
-- name    : GlobalTheory.isSmoothAt_of_finrank_cotangent_le_of_perfectField
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:43:33.166188+00:00
-- url     : https://prove2.me/theorems/1fca34cc-3fc2-4ef0-91de-29a4f8734b75
-- title:
--   Global Theory: is Smooth At of finrank cotangent le of perfect Field
-- statement:
--   The Global Theory construction uses the is Smooth At of finrank cotangent le of perfect Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanFinrankMaximalIdealLeNcardOfLeSupSq.lean#L259-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanFinrankMaximalIdealLeNcardOfLeSupSq.lean#L259-L273

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

theorem GlobalTheory.isSmoothAt_of_finrank_cotangent_le_of_perfectField (k : Type*) [Field k] [PerfectField k]
    {A : Type*} [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (m : Ideal A) [m.IsMaximal]
    {d : ℕ} (h₁ : (d : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime m))
    (h₂ : Module.finrank (A ⧸ m) m.Cotangent ≤ d) :
    IsRegularLocalRing (Localization.AtPrime m) ∧ ringKrullDim (Localization.AtPrime m) = d ∧
      Module.finrank (A ⧸ m) m.Cotangent = d ∧ Algebra.IsSmoothAt k m ∧
      Module.Free (Localization.AtPrime m) Ω[Localization.AtPrime m⁄k] ∧
      Module.finrank (Localization.AtPrime m) Ω[Localization.AtPrime m⁄k] = d := by sorry
