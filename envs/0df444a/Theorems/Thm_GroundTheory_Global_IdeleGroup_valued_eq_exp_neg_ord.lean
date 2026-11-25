-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_valued_eq_exp_neg_ord
-- name    : GroundTheory.Global.IdeleGroup.valued_eq_exp_neg_ord
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:13:22.706245+00:00
-- url     : https://prove2.me/theorems/775657d9-3dbd-45b7-8f32-c8a9e7b95e15
-- title:
--   Idele Group: valued eq exp neg ord
-- statement:
--   The Idele Group construction uses the valued eq exp neg ord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L151-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L151-L153

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleAction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
local notation "𝓘" => (FractionalIdeal (𝓞 K)⁰ K)ˣ

theorem GroundTheory.Global.IdeleGroup.valued_eq_exp_neg_ord (v : HeightOneSpectrum (𝓞 K)) (s : IdeleGroup K) :
    Valued.v ((s : 𝔸[K]).2 v) = exp (-ord v s) := by sorry
