-- Prove2me | Theorems.Thm_GlobalTheory_AffineThickening_Lifts_pow
-- name    : GlobalTheory.AffineThickening.Lifts.pow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:57:29.948818+00:00
-- url     : https://prove2.me/theorems/d36d4d36-8866-4157-9e0c-e40ca6474db9
-- title:
--   Lifts: pow
-- statement:
--   The Lifts construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L66-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L66-L68

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

theorem GlobalTheory.AffineThickening.Lifts.pow (ha : Lifts i U a r) (n : ℕ) : Lifts i U (a ^ n) (r ^ n) := by sorry
