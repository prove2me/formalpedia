-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_im_eq_of_span
-- name    : GlobalTheory.PeriodChart.im_eq_of_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:50.19455+00:00
-- url     : https://prove2.me/theorems/418d73a3-1bfc-4568-ae5a-72a1f291e04f
-- title:
--   Period Chart: im eq of span
-- statement:
--   The Period Chart construction uses the im eq of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L391-L427
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L391-L427

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

theorem GlobalTheory.PeriodChart.im_eq_of_span (P : M → (Fin g → ℂ)) (hs : Submodule.span ℝ (Set.range P) = ⊤)
    (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) →ₗ⋆[ℂ] ℂ) (S T S' T' : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ))
    (h : ∀ a b, (F (S (P a)) (T (P b))).im = (F' (S' (P a)) (T' (P b))).im) (z w : Fin g → ℂ) :
    (F (S z) (T w)).im = (F' (S' z) (T' w)).im := by sorry
