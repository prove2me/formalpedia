-- Prove2me | Theorems.Thm_GlobalTheory_AffineThickening_exists_lifts
-- name    : GlobalTheory.AffineThickening.exists_lifts
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:58:13.462844+00:00
-- url     : https://prove2.me/theorems/0cb5c1a8-ad9e-468b-9e4a-459414e5173a
-- title:
--   Affine Thickening: exists lifts
-- statement:
--   The Affine Thickening construction uses the exists lifts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L100-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L100-L102

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

theorem GlobalTheory.AffineThickening.exists_lifts [IsClosedImmersion i] {U : Y.Opens} (hU : IsAffineOpen U) (r : Γ(Z, ⊤)) :
    ∃ a, Lifts i U a r := by sorry
