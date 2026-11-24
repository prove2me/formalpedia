-- Prove2me | Theorems.Thm_GlobalTheory_IntersectionSymm_terms_ne_top
-- name    : GlobalTheory.IntersectionSymm.terms_ne_top
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:19:58.814685+00:00
-- url     : https://prove2.me/theorems/9bdfdfd2-e6db-41ec-bdd5-076f252f5119
-- title:
--   Intersection Symm: terms ne top
-- statement:
--   The Intersection Symm construction uses the terms ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthSumHeightOneDisjointDivisors.lean#L170-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthSumHeightOneDisjointDivisors.lean#L170-L182

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthKerCokerLsmulQuotientSpanSwapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthSumHeightOneDisjointDivisors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.IntersectionSymm

theorem GlobalTheory.IntersectionSymm.terms_ne_top {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : ringKrullDim A = 2) (a b : A) (ha : a ≠ 0) (P Q : Finset (PrimeSpectrum A))
    (hP : ∀ p, p ∈ P ↔ p.asIdeal.height = 1 ∧ a ∈ p.asIdeal)
    (hQ : ∀ p, p ∈ Q ↔ p.asIdeal.height = 1 ∧ b ∈ p.asIdeal) (hdis : Disjoint P Q) :
    ∀ p ∈ P, Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⧸
          Ideal.span {algebraMap A (Localization.AtPrime p.asIdeal) a}) *
        Module.length (A ⧸ p.asIdeal) ((A ⧸ p.asIdeal) ⧸
          Ideal.span {Ideal.Quotient.mk p.asIdeal b}) ≠ ⊤ := by sorry
