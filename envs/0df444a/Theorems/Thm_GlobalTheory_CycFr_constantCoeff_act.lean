-- Prove2me | Theorems.Thm_GlobalTheory_CycFr_constantCoeff_act
-- name    : GlobalTheory.CycFr.constantCoeff_act
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:01:30.601482+00:00
-- url     : https://prove2.me/theorems/bd514b1a-cd46-503d-9d39-3758be464adc
-- title:
--   Cyc Fr: constant Coeff act
-- statement:
--   The Cyc Fr construction uses the constant Coeff act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L113-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L113-L114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.CycFr
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
variable {O}
open PowerSeries
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
variable {O}

theorem GlobalTheory.CycFr.constantCoeff_act (c : ℤ_[l]) (a : O⟦X⟧) : constantCoeff (_root_.GlobalTheory.CycFr.act O c a) = constantCoeff a := by sorry
