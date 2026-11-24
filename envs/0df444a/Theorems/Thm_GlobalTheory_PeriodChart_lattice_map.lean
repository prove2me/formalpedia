-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_lattice_map
-- name    : GlobalTheory.PeriodChart.lattice_map
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:42:18.535415+00:00
-- url     : https://prove2.me/theorems/4e9df9e2-59cd-40b7-95f2-81979aa49f6e
-- title:
--   Period Chart: lattice map
-- statement:
--   The Period Chart construction uses the lattice map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L480-L507
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L480-L507

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

theorem GlobalTheory.PeriodChart.lattice_map (P P' : M →+ (Fin g → ℂ)) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤)
    (T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) (hT : Function.Injective T) (h : ∀ a, P' a = T (P a)) :
    Function.Injective P' ∧ DiscreteTopology P'.range ∧ Submodule.span ℝ (Set.range P') = ⊤ := by sorry
