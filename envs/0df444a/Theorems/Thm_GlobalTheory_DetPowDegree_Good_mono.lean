-- Prove2me | Theorems.Thm_GlobalTheory_DetPowDegree_Good_mono
-- name    : GlobalTheory.DetPowDegree.Good.mono
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:33:40.566833+00:00
-- url     : https://prove2.me/theorems/ef9e602d-4c17-47b4-bb60-c19456124776
-- title:
--   Good: mono
-- statement:
--   The Good construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetFrobeniusSubPowSupport.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetFrobeniusSubPowSupport.lean#L27-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetFrobeniusSubPowSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh MvPolynomial
open GlobalTheory GlobalTheory.DetPowDegree
variable {α : Type} [Fintype α]
variable {l : ℤ} {L E : ℕ}

theorem GlobalTheory.DetPowDegree.Good.mono {n n' d s : ℕ} {p : MvPolynomial (α ⊕ α) ℤ} (h : Good l L E n d s p)
    (hn : n ≤ n') : Good l L E n' d s p := by sorry
