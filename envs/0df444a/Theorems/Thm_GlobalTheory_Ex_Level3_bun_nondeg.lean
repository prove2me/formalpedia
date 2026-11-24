-- Prove2me | Theorems.Thm_GlobalTheory_Ex_Level3_bun_nondeg
-- name    : GlobalTheory.Ex.Level3.bun_nondeg
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:06:18.676416+00:00
-- url     : https://prove2.me/theorems/1f8cfef2-1734-4289-b950-69cdcf2d516c
-- title:
--   Level3: bun nondeg
-- statement:
--   The Level3 construction uses the bun nondeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/SepticCharacterInjective.lean#L577-L581
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/SepticCharacterInjective.lean#L577-L581

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
open GlobalTheory.Ex.Level3

theorem GlobalTheory.Ex.Level3.bun_nondeg (f : Multiplicative (ZMod 3) →* Oˣ) (hf : Function.Injective f) (s : A₃ → O) (b : A₃)
    (hb : ∀ b' : A₃, (bun f s).weil 3 b b' = 1) : b = 1 := by sorry
