-- Prove2me | Theorems.Thm_GlobalTheory_AffineThickening_isAffineOpen_inf
-- name    : GlobalTheory.AffineThickening.isAffineOpen_inf
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:57:27.714564+00:00
-- url     : https://prove2.me/theorems/14442ef7-168f-4b59-a503-456553741d8a
-- title:
--   Affine Thickening: is Affine Open inf
-- statement:
--   The Affine Thickening construction uses the is Affine Open inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L109-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L109-L114

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

theorem GlobalTheory.AffineThickening.isAffineOpen_inf [IsClosedImmersion i] [Surjective i] {U D : Y.Opens}
    (hU : IsAffineOpen U) {r : Γ(Z, ⊤)} (hD : i ⁻¹ᵁ D = Z.basicOpen r) :
    IsAffineOpen (U ⊓ D) := by sorry
