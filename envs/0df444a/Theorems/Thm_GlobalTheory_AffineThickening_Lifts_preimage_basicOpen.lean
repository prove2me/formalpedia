-- Prove2me | Theorems.Thm_GlobalTheory_AffineThickening_Lifts_preimage_basicOpen
-- name    : GlobalTheory.AffineThickening.Lifts.preimage_basicOpen
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:57:33.051776+00:00
-- url     : https://prove2.me/theorems/7888eae4-5e8d-4a12-baba-b345ab0b94f2
-- title:
--   Lifts: preimage basic Open
-- statement:
--   The Lifts construction uses the preimage basic Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L89-L91

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
open GlobalTheory.AffineThickening.Lifts
variable {U V : Y.Opens} {a b : Γ(Y, U)} {r s : Γ(Z, ⊤)}

theorem GlobalTheory.AffineThickening.Lifts.preimage_basicOpen (ha : Lifts i U a r) :
    i ⁻¹ᵁ Y.basicOpen a = i ⁻¹ᵁ U ⊓ Z.basicOpen r := by sorry
