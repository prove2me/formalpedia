-- Prove2me | Theorems.Thm_GlobalTheory_ChainCoord_ord_of_step
-- name    : GlobalTheory.ChainCoord.ord_of_step
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:38:43.768553+00:00
-- url     : https://prove2.me/theorems/980fbe83-7f3a-4163-9b82-1802fec030b9
-- title:
--   Chain Coord: ord of step
-- statement:
--   The Chain Coord construction uses the ord of step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainLemmaMultivariatePowerSeriesCoordinateForm.lean#L119-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainLemmaMultivariatePowerSeriesCoordinateForm.lean#L119-L161

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PsWeightCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightedOrderGePrimePowOfSumPurePowersAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh MvPowerSeries
open GlobalTheory GlobalTheory.ChainCoord
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ}

theorem GlobalTheory.ChainCoord.ord_of_step {d l : ℕ} (hl : 2 ≤ l) (al : Fin d → ℕ → Fin d → C)
    (h0 : ∀ c e, al c 0 e = if c = e then 1 else 0)
    (t μ z : Fin d → MvPowerSeries (Fin M) C) (ht : ∀ c, constantCoeff (t c) = 0)
    (hμ : ∀ c, constantCoeff (μ c) = 0) (hz : ∀ e, lgSum l al t e = z e) (w : ℝ)
    (step : ∀ t' : Fin d → MvPowerSeries (Fin M) C, (∀ c, OrdGe v ρ (t' c - μ c) w) →
      ∀ N e, OrdGe v ρ (z e - (∑ n ∈ Finset.range (N + 2), ∑ c,
        MvPowerSeries.C (R := C) (al c (n + 1) e) * t' c ^ (l ^ (n + 1))) - μ e) w) :
    ∀ c, OrdGe v ρ (t c - μ c) w := by sorry
