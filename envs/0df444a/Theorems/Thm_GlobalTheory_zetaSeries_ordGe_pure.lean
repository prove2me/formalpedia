-- Prove2me | Theorems.Thm_GlobalTheory_zetaSeries_ordGe_pure
-- name    : GlobalTheory.zetaSeries_ordGe_pure
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:54:47.255103+00:00
-- url     : https://prove2.me/theorems/dcef3553-38d8-44f6-93f1-a7c5ab0a7285
-- title:
--   Global Theory: zeta Series ord Ge pure
-- statement:
--   The Global Theory construction uses the zeta Series ord Ge pure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ZetaSeriesCoeffMulLe.lean#L61-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ZetaSeriesCoeffMulLe.lean#L61-L81

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightedOrderGePrimePowOfSumPurePowersAddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ZetaSeriesCoeffMulLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
open GlobalTheory

theorem GlobalTheory.zetaSeries_ordGe_pure {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {M : ℕ}
    (N : ℕ) (r w : ℝ) (a : Fin M → C) (ha : ∀ j, ((w - r * N : ℝ) : WithTop ℝ) ≤ v (a j)) :
    OrdGe v (fun _ => r)
      (∑ j, MvPowerSeries.C (R := C) (a j) * (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ N) w := by sorry
