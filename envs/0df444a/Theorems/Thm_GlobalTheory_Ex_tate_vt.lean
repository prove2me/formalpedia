-- Prove2me | Theorems.Thm_GlobalTheory_Ex_tate_vt
-- name    : GlobalTheory.Ex.tate_vt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:05:27.35426+00:00
-- url     : https://prove2.me/theorems/2a041688-ce39-5aa7-bb17-54d21a0f8fe0
-- title:
--   Ex: tate vt
-- statement:
--   The Ex construction uses the tate vt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/SepticCharacterInjective.lean#L490-L491
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/SepticCharacterInjective.lean#L490-L491

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

theorem GlobalTheory.Ex.tate_vt (q : Oˣ) (t : Multiplicative ℤ →* Oˣ) (n : ℤ) :
    (tate q).vt ((tate q).tor t) n = (q ^ n ^ 2 * t (Multiplicative.ofAdd n) : Oˣ) := by sorry
