-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumD_c_nsmul
-- name    : GlobalTheory.Ex.NumD.c_nsmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:31:38.863796+00:00
-- url     : https://prove2.me/theorems/c8acc0b4-52c6-4d00-b096-0c45c27c414c
-- title:
--   Num D: c nsmul
-- statement:
--   The Num D construction uses the c nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/SepticCharacterInjective.lean#L99-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/SepticCharacterInjective.lean#L99-L102

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

theorem GlobalTheory.Ex.NumD.c_nsmul (k : ℕ) (a : N.X) : N.c (k • a) = N.c a ^ k := by sorry
