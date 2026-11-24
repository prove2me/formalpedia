-- Prove2me | Theorems.Thm_GlobalTheory_AffineThickening_Lifts_mul_zero
-- name    : GlobalTheory.AffineThickening.Lifts.mul_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:58:20.476151+00:00
-- url     : https://prove2.me/theorems/e3ff19db-2e33-4fd0-93de-a470412abced
-- title:
--   Lifts: mul zero
-- statement:
--   The Lifts construction uses the mul zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L81-L83

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

theorem GlobalTheory.AffineThickening.Lifts.mul_zero (a : Γ(Y, U)) (hb : Lifts i U b 0) : Lifts i U (a * b) 0 := by sorry
