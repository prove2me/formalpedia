-- Prove2me | Theorems.Thm_GlobalTheory_Desc_exists_finiteType_away_of_atPrime
-- name    : GlobalTheory.Desc.exists_finiteType_away_of_atPrime
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:04:22.038382+00:00
-- url     : https://prove2.me/theorems/6de3b7a7-a345-4e0c-8935-fa5b2b41c51d
-- title:
--   Desc: exists finite Type away of at Prime
-- statement:
--   The Desc construction uses the exists finite Type away of at Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteTypeAwayOfAtPrime.lean#L165-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteTypeAwayOfAtPrime.lean#L165-L194

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteTypeAwayOfAtPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Desc
open scoped TensorProduct

theorem GlobalTheory.Desc.exists_finiteType_away_of_atPrime (R C : Type) [CommRing R] [IsNoetherianRing R]
    [CommRing C] [IsDomain C] [Algebra R C] (f : R) (𝔭 : Ideal R) [𝔭.IsPrime]
    (hf : algebraMap R C f ≠ 0)
    (h₁ : Algebra.FiniteType R (Localization.Away (algebraMap R C f)))
    (h₂ : Algebra.FiniteType (Localization.AtPrime 𝔭)
      (TensorProduct R (Localization.AtPrime 𝔭) C)) :
    ∃ g : R, g ∉ 𝔭 ∧ Algebra.FiniteType R (Localization.Away (algebraMap R C g)) := by sorry
