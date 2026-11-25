-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_count_smul
-- name    : GroundTheory.Global.IdeleGroup.count_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:40:00.335199+00:00
-- url     : https://prove2.me/theorems/daadfa62-c3a3-4e9a-969e-b6b098e24fd8
-- title:
--   Idele Group: count smul
-- statement:
--   The Idele Group construction uses the count smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L186-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L186-L190

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

theorem GroundTheory.Global.IdeleGroup.count_smul (v : HeightOneSpectrum (𝓞 K)) (s : IdeleGroup K) (I : 𝓘) :
    count K v ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) =
      ord v s + count K v (I : FractionalIdeal (𝓞 K)⁰ K) := by sorry
