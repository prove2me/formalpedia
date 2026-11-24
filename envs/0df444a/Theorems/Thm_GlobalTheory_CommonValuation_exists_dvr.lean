-- Prove2me | Theorems.Thm_GlobalTheory_CommonValuation_exists_dvr
-- name    : GlobalTheory.CommonValuation.exists_dvr
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:17:13.176573+00:00
-- url     : https://prove2.me/theorems/58f1f5f1-7368-4b88-9d8f-173929c25558
-- title:
--   Common Valuation: exists dvr
-- statement:
--   The Common Valuation construction uses the exists dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RamificationIndexValuationCompat.lean#L49-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RamificationIndexValuationCompat.lean#L49-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteSeparableCompositum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RamificationIndexValuationCompat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CommonValuation

theorem GlobalTheory.CommonValuation.exists_dvr (V K L : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra W L)
      (_ : IsFractionRing W L) (f : V →+* W), (∀ z : V, algebraMap W L (f z) = algebraMap K L (algebraMap V K z)) ∧
      ∀ z : V, f z ∈ IsLocalRing.maximalIdeal W ↔ z ∈ IsLocalRing.maximalIdeal V := by sorry
