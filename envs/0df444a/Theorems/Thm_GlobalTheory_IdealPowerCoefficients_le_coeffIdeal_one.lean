-- Prove2me | Theorems.Thm_GlobalTheory_IdealPowerCoefficients_le_coeffIdeal_one
-- name    : GlobalTheory.IdealPowerCoefficients.le_coeffIdeal_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:05:20.117227+00:00
-- url     : https://prove2.me/theorems/8e87e0f1-bea8-4e26-9cdf-111bc0328072
-- title:
--   Ideal Power Coefficients: le coeff Ideal one
-- statement:
--   The Ideal Power Coefficients construction uses the le coeff Ideal one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MemPowIffCoeffMem.lean#L51-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MemPowIffCoeffMem.lean#L51-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemPowIffCoeffMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.IdealPowerCoefficients
open MvPowerSeries Finsupp
variable {R : Type u_1} [CommRing R] {κ : Type u_2}

theorem GlobalTheory.IdealPowerCoefficients.le_coeffIdeal_one (I : Ideal R) :
    Ideal.map C I ⊔ Ideal.span (Set.range X) ≤ coeffIdeal (κ := κ) I 1 := by sorry
