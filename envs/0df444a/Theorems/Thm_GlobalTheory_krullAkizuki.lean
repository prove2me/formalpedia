-- Prove2me | Theorems.Thm_GlobalTheory_krullAkizuki
-- name    : GlobalTheory.krullAkizuki
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:25.100737+00:00
-- url     : https://prove2.me/theorems/8525b2ee-92ed-46b5-af57-1b34449a6926
-- title:
--   Global Theory: krull Akizuki
-- statement:
--   The Global Theory construction uses the krull Akizuki property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L515-L545
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L515-L545

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.DimensionLEOne A]
  (K : Type*) {L : Type*} [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L]
  [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
include K

theorem GlobalTheory.krullAkizuki (B : Subalgebra A L) : IsNoetherianRing B ∧ Ring.DimensionLEOne B := by sorry
