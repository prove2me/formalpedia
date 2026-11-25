-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_diagonal_smul
-- name    : GroundTheory.Global.IdeleGroup.coe_diagonal_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:54:47.76799+00:00
-- url     : https://prove2.me/theorems/0e4d2966-8d0a-53da-8acb-5e51e8dbe8e1
-- title:
--   Idele Group: coe diagonal smul
-- statement:
--   The Idele Group construction uses the coe diagonal smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L221-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L221-L224

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

theorem GroundTheory.Global.IdeleGroup.coe_diagonal_smul (a : Kˣ) (I : 𝓘) :
    ((diagonal K a • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) =
      spanSingleton (𝓞 K)⁰ (a : K) * I := by sorry
