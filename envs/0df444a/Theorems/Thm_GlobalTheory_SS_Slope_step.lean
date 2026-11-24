-- Prove2me | Theorems.Thm_GlobalTheory_SS_Slope_step
-- name    : GlobalTheory.SS.Slope.step
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:36:19.550947+00:00
-- url     : https://prove2.me/theorems/ad0d12a4-5798-414c-a80d-b8878deb6116
-- title:
--   Slope: step
-- statement:
--   The Slope construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/WeightedOrderSlopeComparison.lean#L50-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/WeightedOrderSlopeComparison.lean#L50-L112

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_WeightedOrderSlopeComparison
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Slope
open MvPowerSeries
variable {k : Type} [Field k]

theorem GlobalTheory.SS.Slope.step (f d : MvPowerSeries (Fin 2) k) (hf : ∀ t : Fin 2 →₀ ℕ, coeff t f ≠ 0 → 1 ≤ t 1)
    (s₀ : Fin 2 →₀ ℕ) (hs₀ : coeff s₀ d ≠ 0) (hs₀' : s₀ 1 = 0) (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)
    (h : weightedOrder (![m, n] : Fin 2 → ℕ) f < weightedOrder (![m, n] : Fin 2 → ℕ) d) :
    ∃ p, n * (s₀ 0).factorial < m * p ∧
      ¬ weightedOrder (![(s₀ 0).factorial, p] : Fin 2 → ℕ) d <
        weightedOrder (![(s₀ 0).factorial, p] : Fin 2 → ℕ) f := by sorry
