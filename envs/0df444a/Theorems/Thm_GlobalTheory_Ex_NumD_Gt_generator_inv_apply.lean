-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumD_Gt_generator_inv_apply
-- name    : GlobalTheory.Ex.NumD.Gt.generator_inv_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:06:09.413129+00:00
-- url     : https://prove2.me/theorems/4b2d96cd-cb98-576c-975b-321533a22adc
-- title:
--   Gt: generator inv apply
-- statement:
--   The Gt construction uses the generator inv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/SepticCharacterInjective.lean#L192-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/SepticCharacterInjective.lean#L192-L192

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
open GlobalTheory.Ex.NumD.Gt
variable {N}

theorem GlobalTheory.Ex.NumD.Gt.generator_inv_apply (g : N.Gt) (χ : N.X) : g⁻¹.s χ = N.θ (N.c χ) g.b g.b⁻¹ / g.s χ := by sorry
