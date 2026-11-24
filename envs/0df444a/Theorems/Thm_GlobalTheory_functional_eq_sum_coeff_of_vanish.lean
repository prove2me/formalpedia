-- Prove2me | Theorems.Thm_GlobalTheory_functional_eq_sum_coeff_of_vanish
-- name    : GlobalTheory.functional_eq_sum_coeff_of_vanish
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:55:05.341116+00:00
-- url     : https://prove2.me/theorems/afefbbab-5bd1-47ef-bcd2-eb476405568c
-- title:
--   Global Theory: functional eq sum coeff of vanish
-- statement:
--   The Global Theory construction uses the functional eq sum coeff of vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/NabValNEqSumCoeff.lean#L10-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/NabValNEqSumCoeff.lean#L10-L34

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NablaValueCopiesBilinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_InvariantValueCopiesEqZeroOfLowCoeffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NabValNEqSumCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory

theorem GlobalTheory.functional_eq_sum_coeff_of_vanish {σ K : Type} [CommRing K] [Finite σ]
    (F : MvPowerSeries σ K → K) (N : ℕ)
    (hadd : ∀ f g, F (f + g) = F f + F g) (hsmul : ∀ (t : K) f, F (t • f) = t * F f)
    (hvan : ∀ f, (∀ μ : σ →₀ ℕ, μ.degree ≤ N → MvPowerSeries.coeff μ f = 0) → F f = 0) :
    ∃ S : Finset (σ →₀ ℕ), ∀ f, F f =
      ∑ μ ∈ S, MvPowerSeries.coeff μ f * F (MvPowerSeries.monomial μ (1 : K)) := by sorry
