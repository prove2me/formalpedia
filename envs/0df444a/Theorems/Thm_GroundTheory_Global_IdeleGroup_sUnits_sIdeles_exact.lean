-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_sUnits_sIdeles_exact
-- name    : GroundTheory.Global.IdeleGroup.sUnits_sIdeles_exact
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:55:06.1572+00:00
-- url     : https://prove2.me/theorems/4f7fcffd-1612-5bb8-8233-4616fc535ad7
-- title:
--   Idele Group: s Units s Ideles exact
-- statement:
--   The Idele Group construction uses the s Units s Ideles exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/SIdeleGroups.lean#L134-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/SIdeleGroups.lean#L134-L139

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleGroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable (S : Set (HeightOneSpectrum (𝓞 K)))

theorem GroundTheory.Global.IdeleGroup.sUnits_sIdeles_exact (h : (diagonal K).range ⊔ sIdeles S = ⊤) :
    Function.Injective (sUnitsToSIdeles S) ∧
      (sUnitsToSIdeles S).range = (sIdelesToIdeleClassGroup S).ker ∧
      Function.Surjective (sIdelesToIdeleClassGroup S) := by sorry
