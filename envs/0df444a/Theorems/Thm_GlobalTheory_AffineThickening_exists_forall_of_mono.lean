-- Prove2me | Theorems.Thm_GlobalTheory_AffineThickening_exists_forall_of_mono
-- name    : GlobalTheory.AffineThickening.exists_forall_of_mono
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:58:34.370502+00:00
-- url     : https://prove2.me/theorems/668a5c54-39e9-4616-8c9e-3dbf8cd1fbcd
-- title:
--   Affine Thickening: exists forall of mono
-- statement:
--   The Affine Thickening construction uses the exists forall of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L116-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L116-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open GlobalTheory GlobalTheory.AffineThickening
variable {Z Y : Scheme.{u}} (i : Z ⟶ Y)
variable {i}

theorem GlobalTheory.AffineThickening.exists_forall_of_mono {α : Type*} [Finite α] (P : α → ℕ → Prop)
    (hP : ∀ a n, P a n → P a (n + 1)) (h : ∀ a, ∃ n, P a n) : ∃ n, ∀ a, P a n := by sorry
