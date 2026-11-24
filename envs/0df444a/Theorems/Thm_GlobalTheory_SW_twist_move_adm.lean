-- Prove2me | Theorems.Thm_GlobalTheory_SW_twist_move_adm
-- name    : GlobalTheory.SW.twist_move_adm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:45:17.897801+00:00
-- url     : https://prove2.me/theorems/964e5ca9-0515-4655-bb77-92f97a02479d
-- title:
--   SW: twist move adm
-- statement:
--   The SW construction uses the twist move adm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalMatrixMoveAdmissibleUniformLevel.lean#L176-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalMatrixMoveAdmissibleUniformLevel.lean#L176-L201

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
open GlobalTheory.SW.TwistMove

theorem GlobalTheory.SW.twist_move_adm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ), ∃ (c : ℕ) (C : ℝ), 0 < c ∧ ∀ (n M R : ℕ) (φ : Fam E n N) (𝔛 : Lt E N), admitted M R φ → 𝔛.FG → Agree (R * M) 𝔛 (stdL E N) → ∃ a : Matrix (Fin N) (Fin N) E, a.det ≠ 0 ∧ gidx 𝔛 ≤ C * |(Algebra.norm ℚ a.det : ℝ)| ∧ admitted M (R * c) (fun Λ x => twist R 𝔛 φ Λ (x * a)) := by sorry
