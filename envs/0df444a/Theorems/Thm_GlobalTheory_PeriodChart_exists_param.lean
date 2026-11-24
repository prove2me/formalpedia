-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_exists_param
-- name    : GlobalTheory.PeriodChart.exists_param
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:42:45.26089+00:00
-- url     : https://prove2.me/theorems/2188e40c-b96e-400b-8af6-519bf50abef3
-- title:
--   Period Chart: exists param
-- statement:
--   The Period Chart construction uses the exists param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L138-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L138-L209

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

theorem GlobalTheory.PeriodChart.exists_param {ι : Type} [Fintype ι] (R : ι → ι → Prop) (s : ι → Prop) (hR : ∀ i j, R i j → R j i)
    (hs : ∀ i j, R i j → (s i ↔ ¬ s j)) :
    ∃ (m : ℕ) (L : (Fin m → ℂ) →ₗ[ℂ] Matrix ι ι ℂ), 2 * m = Nat.card {x : ι × ι // R x.1 x.2} ∧
      Function.Injective L ∧ ∀ W : Matrix ι ι ℂ, (∃ b, L b = W) ↔ Wᵀ = W ∧ ∀ i j, ¬ R i j → W i j = 0 := by sorry
