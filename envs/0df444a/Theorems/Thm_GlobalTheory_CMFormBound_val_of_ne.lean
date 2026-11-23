-- Prove2me | Theorems.Thm_GlobalTheory_CMFormBound_val_of_ne
-- name    : GlobalTheory.CMFormBound.val_of_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:25.878037+00:00
-- url     : https://prove2.me/theorems/37c80a57-85f3-4488-ab50-c9d918f4ed71
-- title:
--   CMForm Bound: val of ne
-- statement:
--   The CMForm Bound construction uses the val of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodGaloisIntegral.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodGaloisIntegral.lean#L44-L46

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

theorem GlobalTheory.CMFormBound.val_of_ne (l : ℕ) {x : K} (hx : x ≠ 0) :
    val_vp O l x = (((ord_vw O x : ℚ) / (ord_vw O (l : K) : ℚ) : ℚ) : WithTop ℚ) := by sorry
