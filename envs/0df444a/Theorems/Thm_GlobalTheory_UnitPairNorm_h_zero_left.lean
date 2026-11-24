-- Prove2me | Theorems.Thm_GlobalTheory_UnitPairNorm_h_zero_left
-- name    : GlobalTheory.UnitPairNorm.h_zero_left
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:38:57.38162+00:00
-- url     : https://prove2.me/theorems/f42a1520-ea19-409d-b881-1a95817af946
-- title:
--   Unit Pair Norm: h zero left
-- statement:
--   The Unit Pair Norm construction uses the h zero left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitNorm.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitNorm.lean#L28-L31

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitPairNorm
open Module
variable {O E : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E]
  [Algebra O E] [IsFractionRing O E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]

theorem GlobalTheory.UnitPairNorm.h_zero_left (h : V → V → E) (hsmul : ∀ (s : E) (x z : V), h (s • x) z = s * h x z)
    (z : V) : h 0 z = 0 := by sorry
