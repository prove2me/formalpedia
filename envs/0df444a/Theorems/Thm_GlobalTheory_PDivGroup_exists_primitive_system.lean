-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_exists_primitive_system
-- name    : GlobalTheory.PDivGroup.exists_primitive_system
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:56:47.132796+00:00
-- url     : https://prove2.me/theorems/56c1d9b9-15b5-41a7-95b1-6935ecb9c262
-- title:
--   PDiv Group: exists primitive system
-- statement:
--   The PDiv Group construction uses the exists primitive system property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L429-L450
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L429-L450

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv TateFree
variable {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O)
variable (C : Type) [Field C] [Algebra O C] [IsIntegrallyClosedIn O C] [IsAlgClosed C]
  [CharZero C]
include C
variable [Fact p.Prime]
variable (p O)

theorem GlobalTheory.PDivGroup.exists_primitive_system : ∃ ζ : ℕ → O, ζ 0 = 1 ∧ (∀ n, ζ (n + 1) ^ p = ζ n) ∧
    ∀ n, IsPrimitiveRoot (ζ n) (p ^ n) := by sorry
