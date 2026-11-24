-- Prove2me | Theorems.Thm_GlobalTheory_AffineThickening_Lifts_basicOpen_eq
-- name    : GlobalTheory.AffineThickening.Lifts.basicOpen_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:57:49.825017+00:00
-- url     : https://prove2.me/theorems/be498a5a-f1a2-4f11-9f92-da66207b65ae
-- title:
--   Lifts: basic Open eq
-- statement:
--   The Lifts construction uses the basic Open eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L104-L107

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

theorem GlobalTheory.AffineThickening.Lifts.basicOpen_eq [Surjective i] {U D : Y.Opens} {a : Γ(Y, U)} {r : Γ(Z, ⊤)}
    (ha : Lifts i U a r) (hD : i ⁻¹ᵁ D = Z.basicOpen r) : U ⊓ D = Y.basicOpen a := by sorry
