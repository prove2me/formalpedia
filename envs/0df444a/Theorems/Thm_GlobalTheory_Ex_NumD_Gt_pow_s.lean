-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumD_Gt_pow_s
-- name    : GlobalTheory.Ex.NumD.Gt.pow_s
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:18.581841+00:00
-- url     : https://prove2.me/theorems/cc7332f6-339c-4ca2-badc-4a927218530d
-- title:
--   Gt: pow s
-- statement:
--   The Gt construction uses the pow s property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/SepticCharacterInjective.lean#L204-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/SepticCharacterInjective.lean#L204-L210

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

theorem GlobalTheory.Ex.NumD.Gt.pow_s (g : N.Gt) (k : ℕ) (χ : N.X) : (g ^ k).s χ * cubN N.θ k 1 g.b (N.c χ) = g.s χ ^ k := by sorry
