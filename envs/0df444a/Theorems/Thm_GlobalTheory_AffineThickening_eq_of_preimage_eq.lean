-- Prove2me | Theorems.Thm_GlobalTheory_AffineThickening_eq_of_preimage_eq
-- name    : GlobalTheory.AffineThickening.eq_of_preimage_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:58:43.34414+00:00
-- url     : https://prove2.me/theorems/65f26910-0061-45fc-96fb-810cd3315bb6
-- title:
--   Affine Thickening: eq of preimage eq
-- statement:
--   The Affine Thickening construction uses the eq of preimage eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L95-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L95-L98

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

theorem GlobalTheory.AffineThickening.eq_of_preimage_eq [Surjective i] {U V : Y.Opens} (h : i ⁻¹ᵁ U = i ⁻¹ᵁ V) : U = V := by sorry
