-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_smul_eq_iff_localIdeal
-- name    : GroundTheory.Global.IdeleGroup.smul_eq_iff_localIdeal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:54:56.133867+00:00
-- url     : https://prove2.me/theorems/4a95c34b-efbd-4715-bb05-c7603d0a9264
-- title:
--   Idele Group: smul eq iff local Ideal
-- statement:
--   The Idele Group construction uses the smul eq iff local Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L257-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L257-L266

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

theorem GroundTheory.Global.IdeleGroup.smul_eq_iff_localIdeal (s : IdeleGroup K) (I J : 𝓘) :
    s • I = J ↔ ∀ v : HeightOneSpectrum (𝓞 K), localIdeal (J : FractionalIdeal (𝓞 K)⁰ K) v =
      (localIdeal (I : FractionalIdeal (𝓞 K)⁰ K) v).map
        (LinearMap.mulLeft (v.adicCompletionIntegers K) ((s : 𝔸[K]).2 v)) := by sorry
