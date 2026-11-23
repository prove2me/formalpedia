-- Prove2me | Theorems.Thm_GlobalTheory_PairingBound_ord_alg_nonneg
-- name    : GlobalTheory.PairingBound.ord_alg_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:10:06.015041+00:00
-- url     : https://prove2.me/theorems/fc859551-2b9f-42ff-9e9a-18655945d748
-- title:
--   Pairing Bound: ord alg nonneg
-- statement:
--   The Pairing Bound construction uses the ord alg nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodDenominatorBound.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodDenominatorBound.lean#L16-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodDenominatorBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.PairingBound
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] {K : Type} [Field K] [Algebra O K]
  [IsFractionRing O K]

theorem GlobalTheory.PairingBound.ord_alg_nonneg (x : O) (hx : x ≠ 0) : 0 ≤ ord_vw O (algebraMap O K x) := by sorry
