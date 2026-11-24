-- Prove2me | Theorems.Thm_GlobalTheory_CMFormBound_ord_natCast_ne
-- name    : GlobalTheory.CMFormBound.ord_natCast_ne
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:03:05.763857+00:00
-- url     : https://prove2.me/theorems/5566df57-5562-4c0a-9ed0-fce24b016133
-- title:
--   CMForm Bound: ord nat Cast ne
-- statement:
--   The CMForm Bound construction uses the ord nat Cast ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodGaloisIntegral.lean#L30-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodGaloisIntegral.lean#L30-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodGaloisIntegral
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
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CMFormBound
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K]
  [IsFractionRing O K]

theorem GlobalTheory.CMFormBound.ord_natCast_ne [CharZero O] (l : ℕ) (hl : l ≠ 0) (h : (l : O) ∈ IsLocalRing.maximalIdeal O) : ord_vw O (l : K) ≠ 0 := by sorry
