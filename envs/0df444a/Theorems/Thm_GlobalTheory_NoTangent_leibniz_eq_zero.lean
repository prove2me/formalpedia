-- Prove2me | Theorems.Thm_GlobalTheory_NoTangent_leibniz_eq_zero
-- name    : GlobalTheory.NoTangent.leibniz_eq_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:35:21.325803+00:00
-- url     : https://prove2.me/theorems/93f3a927-3eb6-4a6b-9336-ea8213a16982
-- title:
--   No Tangent: leibniz eq zero
-- statement:
--   The No Tangent construction uses the leibniz eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/AlgHomDualNumberExt.lean#L11-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/AlgHomDualNumberExt.lean#L11-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsAdicCompleteOfFgOfNatCastMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesExistsPolynomialTotalDegreeLeSubMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AlgHomDualNumberExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.NoTangent
open MvPowerSeries

theorem GlobalTheory.NoTangent.leibniz_eq_zero {O C σ : Type} [CommRing O] [CommRing C]
    (φ₀ : MvPowerSeries σ O →+* C) (E : MvPowerSeries σ O →+ C) (a : σ → O)
    (hmul : ∀ g h, E (g * h) = φ₀ g * E h + φ₀ h * E g)
    (hC : ∀ c, E (MvPowerSeries.C c) = 0) (hX : ∀ j, E (X j) = 0)
    (ha : ∀ j, φ₀ (X j - MvPowerSeries.C (a j)) = 0)
    (hP : ∀ g : MvPowerSeries σ O, ∃ P : MvPolynomial σ O,
      g - (P : MvPowerSeries σ O) ∈
        Ideal.span (Set.range fun j => (X j - MvPowerSeries.C (a j) : MvPowerSeries σ O)))
    (g : MvPowerSeries σ O) : E g = 0 := by sorry
