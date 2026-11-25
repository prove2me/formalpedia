-- Prove2me | Theorems.Thm_GlobalTheory_HTLat_map_mkQ_step_succ
-- name    : GlobalTheory.HTLat.map_mkQ_step_succ
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:06:32.768278+00:00
-- url     : https://prove2.me/theorems/903b6c79-291a-4252-94c6-d18383064691
-- title:
--   HTLat: map mk Q step succ
-- statement:
--   The HTLat construction uses the map mk Q step succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L325-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L325-L328

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct NNReal NumberField Pointwise
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.HTLat
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ}

theorem GlobalTheory.HTLat.map_mkQ_step_succ (f : Fin N → U) (i : Fin N) :
    (step C f (i + 1)).map (step C f i).mkQ = Submodule.span C {(step C f i).mkQ (f i)} := by sorry
