-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumD_qEq_iff
-- name    : GlobalTheory.Ex.NumD.qEq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:38:44.854559+00:00
-- url     : https://prove2.me/theorems/57bbc15f-ed5b-4c0a-8ad9-e69e95d7334f
-- title:
--   Num D: q Eq iff
-- statement:
--   The Num D construction uses the q Eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/SepticCharacterInjective.lean#L308-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/SepticCharacterInjective.lean#L308-L310

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

theorem GlobalTheory.Ex.NumD.qEq_iff {k : ℕ} (p p' : N.QT k) : N.QEq p p' ↔ ∃ z, p' = p * N.qTriv k z := by sorry
