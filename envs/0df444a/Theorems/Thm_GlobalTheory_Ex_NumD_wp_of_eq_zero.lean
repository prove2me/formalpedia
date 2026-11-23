-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumD_wp_of_eq_zero
-- name    : GlobalTheory.Ex.NumD.wp_of_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:38:58.99508+00:00
-- url     : https://prove2.me/theorems/8cb0ff58-0d59-4e5f-8b10-e36d7a75c8c5
-- title:
--   Num D: wp of eq zero
-- statement:
--   The Num D construction uses the wp of eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/SepticCharacterInjective.lean#L335-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/SepticCharacterInjective.lean#L335-L337

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

theorem GlobalTheory.Ex.NumD.wp_of_eq_zero {k : ℕ} (p p' : N.QT k) (h : p.1.1.toAdd = 0) (h' : p'.1.1.toAdd = 0) :
    N.wp p p' = N.weil k p.1.2.b p'.1.2.b := by sorry
