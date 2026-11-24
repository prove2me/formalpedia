-- Prove2me | Theorems.Thm_GlobalTheory_Ex_tate_int
-- name    : GlobalTheory.Ex.tate_int
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:08:35.265859+00:00
-- url     : https://prove2.me/theorems/9a57d386-9ad6-415c-b31c-11ecc3f832eb
-- title:
--   Ex: tate int
-- statement:
--   The Ex construction uses the tate int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/SepticCharacterInjective.lean#L510-L529
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/SepticCharacterInjective.lean#L510-L529

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
attribute [instance] NumB.grp
attribute [instance] NumD.add NumD.free NumD.fin
variable {O : Type} [CommRing O]

theorem GlobalTheory.Ex.tate_int {C : Type} [NormedField C] (q : Cˣ) (hq : ‖(q : C)‖ < 1) : (tate q).Int (tateForm q) := by sorry
