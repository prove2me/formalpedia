-- Prove2me | Theorems.Thm_GlobalTheory_SW_TwistMove_gidx_mul_le
-- name    : GlobalTheory.SW.TwistMove.gidx_mul_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:43:58.63157+00:00
-- url     : https://prove2.me/theorems/6efaa86e-b3a2-40dc-a91a-e73086dc7c89
-- title:
--   Twist Move: gidx mul le
-- statement:
--   The Twist Move construction uses the gidx mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalMatrixMoveAdmissibleUniformLevel.lean#L54-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalMatrixMoveAdmissibleUniformLevel.lean#L54-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalMatrixMoveAdmissibleUniformLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TwistMove
open GlobalTheory.SW.TwistAdm
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}

theorem GlobalTheory.SW.TwistMove.gidx_mul_le {𝔛 : Lt E N} {t : ℕ} (ht : 0 < t) (h : ∀ v ∈ stdL E N, (t : E) • v ∈ 𝔛)
    {b : Matrix (Fin N) (Fin N) E} (hb : b.det ≠ 0) (hX : 𝔛.toAddSubgroup ≤ imL b) :
    gidx 𝔛 * |(Algebra.norm ℚ b.det : ℝ)| ≤ 1 := by sorry
