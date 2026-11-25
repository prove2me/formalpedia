-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_sup_sIdeles_eq_top_of_subset
-- name    : GroundTheory.Global.IdeleGroup.sup_sIdeles_eq_top_of_subset
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:55:25.886625+00:00
-- url     : https://prove2.me/theorems/42d6de18-3830-4d1e-ade5-7a9f44cdaed2
-- title:
--   Idele Group: sup s Ideles eq top of subset
-- statement:
--   The Idele Group construction uses the sup s Ideles eq top of subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/SIdeleGroups.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/SIdeleGroups.lean#L58-L60

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

theorem GroundTheory.Global.IdeleGroup.sup_sIdeles_eq_top_of_subset {S T : Set (HeightOneSpectrum (𝓞 K))} (hST : S ⊆ T)
    (h : (diagonal K).range ⊔ sIdeles S = ⊤) : (diagonal K).range ⊔ sIdeles T = ⊤ := by sorry
