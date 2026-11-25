-- Prove2me | Theorems.Thm_GlobalTheory_LegendreBounds_padicValNat_prod_factorial
-- name    : GlobalTheory.LegendreBounds.padicValNat_prod_factorial
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:30:07.155306+00:00
-- url     : https://prove2.me/theorems/a07a47e9-bce3-4ffb-ad45-c8a1f77445d5
-- title:
--   Legendre Bounds: padic Val Nat prod factorial
-- statement:
--   The Legendre Bounds construction uses the padic Val Nat prod factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LegendreBoundsFactorialMultiIndexCapelli.lean#L87-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LegendreBoundsFactorialMultiIndexCapelli.lean#L87-L98

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelli
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.LegendreBounds

theorem GlobalTheory.LegendreBounds.padicValNat_prod_factorial (l : ℕ) (hl : l.Prime) {κ : Type} (s : Finset κ)
    (A : κ → ℕ) :
    (padicValNat l (∏ j ∈ s, (A j).factorial) : ℝ)
      = ∑ j ∈ s, (padicValNat l (A j).factorial : ℝ) := by sorry
