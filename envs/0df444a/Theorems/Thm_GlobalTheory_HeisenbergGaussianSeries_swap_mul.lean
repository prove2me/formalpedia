-- Prove2me | Theorems.Thm_GlobalTheory_HeisenbergGaussianSeries_swap_mul
-- name    : GlobalTheory.HeisenbergGaussianSeries.swap_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:09.791806+00:00
-- url     : https://prove2.me/theorems/7fc42c9b-8f07-4672-b8d4-1db8f7c9a541
-- title:
--   Heisenberg Gaussian Series: swap mul
-- statement:
--   The Heisenberg Gaussian Series construction uses the swap mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ContinuousBicharacterWeilSetup.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ContinuousBicharacterWeilSetup.lean#L42-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExpSeriesContDiffAndHasDerivAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CharSeriesExistsNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SummableGaussianCoset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPosMulNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ContinuousBicharacterWeilSetup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.HeisenbergGaussianSeries

theorem GlobalTheory.HeisenbergGaussianSeries.swap_mul {G : Type} [AddCommGroup G] (β : G → G → ℂ)
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hd : ∀ x, β x x = 1) (x y : G) : β x y * β y x = 1 := by sorry
