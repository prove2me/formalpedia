-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_finrank_of_lattice
-- name    : GlobalTheory.PeriodChart.finrank_of_lattice
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:42:14.934512+00:00
-- url     : https://prove2.me/theorems/71b27125-15f3-453d-835c-6892c5d8948e
-- title:
--   Period Chart: finrank of lattice
-- statement:
--   The Period Chart construction uses the finrank of lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L439-L446
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L439-L446

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {g : ℕ}
variable {M : Type} [AddCommGroup M]

theorem GlobalTheory.PeriodChart.finrank_of_lattice (P : M →+ (Fin g → ℂ)) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤) :
    finrank ℤ M = finrank ℝ (Fin g → ℂ) := by sorry
