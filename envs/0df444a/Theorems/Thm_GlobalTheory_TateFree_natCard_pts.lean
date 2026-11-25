-- Prove2me | Theorems.Thm_GlobalTheory_TateFree_natCard_pts
-- name    : GlobalTheory.TateFree.natCard_pts
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:54:12.572195+00:00
-- url     : https://prove2.me/theorems/6987a527-98fe-4a7f-b7c6-7bafcb594d64
-- title:
--   Tate Free: nat Card pts
-- statement:
--   The Tate Free construction uses the nat Card pts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L47-L50

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
open GlobalTheory.TateFree
variable (O C A : Type) [CommRing O] [Field C] [Algebra O C] [IsIntegrallyClosedIn O C]
  [CommRing A]
variable [IsAlgClosed C] [CharZero C] [HopfAlgebra O A] [Module.Finite O A]

theorem GlobalTheory.TateFree.natCard_pts : Nat.card (A →ₐ[O] O) = finrank C (C ⊗[O] A) := by sorry
