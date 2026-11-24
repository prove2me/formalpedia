-- Prove2me | Theorems.Thm_GlobalTheory_exists_prime_le_notMem_ringKrullDim_eq_one
-- name    : GlobalTheory.exists_prime_le_notMem_ringKrullDim_eq_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:38:16.124227+00:00
-- url     : https://prove2.me/theorems/78fd120e-ebd3-44a6-859d-26a2e014e2fd
-- title:
--   Global Theory: exists prime le not Mem ring Krull Dim eq one
-- statement:
--   The Global Theory construction uses the exists prime le not Mem ring Krull Dim eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsPrimeLeNotMemRingKrullDimEqOne.lean#L7-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsPrimeLeNotMemRingKrullDimEqOne.lean#L7-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsPrimeLeNotMemRingKrullDimEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_prime_le_notMem_ringKrullDim_eq_one :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [IsDomain B] [Algebra k B]
      [Algebra.FiniteType k B] (m : Ideal B) (h : B), m.IsMaximal → h ≠ 0 → h ∈ m →
      ∃ p : Ideal B, p.IsPrime ∧ p ≤ m ∧ h ∉ p ∧ ringKrullDim (B ⧸ p) = 1 := by sorry
