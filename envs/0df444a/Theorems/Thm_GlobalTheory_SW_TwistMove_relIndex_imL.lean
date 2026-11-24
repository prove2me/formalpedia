-- Prove2me | Theorems.Thm_GlobalTheory_SW_TwistMove_relIndex_imL
-- name    : GlobalTheory.SW.TwistMove.relIndex_imL
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:43:59.802976+00:00
-- url     : https://prove2.me/theorems/48bf36ce-6012-4a29-8c97-28005c234e74
-- title:
--   Twist Move: rel Index im L
-- statement:
--   The Twist Move construction uses the rel Index im L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalMatrixMoveAdmissibleUniformLevel.lean#L34-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalMatrixMoveAdmissibleUniformLevel.lean#L34-L52

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

theorem GlobalTheory.SW.TwistMove.relIndex_imL {b₁ b₂ : Matrix (Fin N) (Fin N) E} (h₁ : b₁.det ≠ 0) (h₂ : b₂.det ≠ 0)
    (hle : imL b₁ ≤ imL b₂) :
    ((imL b₁).relIndex (imL b₂) : ℚ) * |Algebra.norm ℚ b₂.det| = |Algebra.norm ℚ b₁.det| := by sorry
