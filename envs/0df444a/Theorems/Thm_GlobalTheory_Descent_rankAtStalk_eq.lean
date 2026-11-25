-- Prove2me | Theorems.Thm_GlobalTheory_Descent_rankAtStalk_eq
-- name    : GlobalTheory.Descent.rankAtStalk_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:04:12.558808+00:00
-- url     : https://prove2.me/theorems/25302c6e-5ad3-4128-b589-4c41ab5d2299
-- title:
--   Descent: rank At Stalk eq
-- statement:
--   The Descent construction uses the rank At Stalk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SpanSingletonEqTopIffIsUnitOfIsBaseChange.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SpanSingletonEqTopIffIsUnitOfIsBaseChange.lean#L48-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
open GlobalTheory.Descent
variable {A : Type*} (A' : Type*) [CommRing A] [CommRing A'] [Algebra A A']
  [Module.FaithfullyFlat A A'] {M : Type*} [AddCommGroup M] [Module A M]

theorem GlobalTheory.Descent.rankAtStalk_eq [Module.Finite A' (A' ⊗[A] M)] [Module.Flat A' (A' ⊗[A] M)] {r : ℕ}
    (h : ∀ q : PrimeSpectrum A', Module.rankAtStalk (A' ⊗[A] M) q = r) (p : PrimeSpectrum A) :
    Module.rankAtStalk M p = r := by sorry
