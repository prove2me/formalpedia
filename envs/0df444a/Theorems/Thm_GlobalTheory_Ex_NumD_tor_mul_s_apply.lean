-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumD_tor_mul_s_apply
-- name    : GlobalTheory.Ex.NumD.tor_mul_s_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:45.78015+00:00
-- url     : https://prove2.me/theorems/c0499523-d2b7-4637-8bc7-3fde2f91bc81
-- title:
--   Num D: tor mul s apply
-- statement:
--   The Num D construction uses the tor mul s apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/SepticCharacterInjective.lean#L279-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/SepticCharacterInjective.lean#L279-L281

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
open GlobalTheory.Ex.NumD
variable (N : NumD O)

theorem GlobalTheory.Ex.NumD.tor_mul_s_apply (t : Multiplicative N.X →* Oˣ) (g : N.Gt) (χ : N.X) :
    (N.tor t * g).s χ = t (Multiplicative.ofAdd χ) * g.s χ := by sorry
