-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_smul_le_smul_iff
-- name    : GroundTheory.Global.IdeleGroup.smul_le_smul_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:55:21.187915+00:00
-- url     : https://prove2.me/theorems/f6311c49-7f42-4bb2-93f5-bd901e0310ee
-- title:
--   Idele Group: smul le smul iff
-- statement:
--   The Idele Group construction uses the smul le smul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L192-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L192-L197

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

theorem GroundTheory.Global.IdeleGroup.smul_le_smul_iff {s : IdeleGroup K} {I J : 𝓘} :
    ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) ≤ (s • J : 𝓘) ↔
      (I : FractionalIdeal (𝓞 K)⁰ K) ≤ J := by sorry
