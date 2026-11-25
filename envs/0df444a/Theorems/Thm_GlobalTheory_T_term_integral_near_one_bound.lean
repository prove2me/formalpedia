-- Prove2me | Theorems.Thm_GlobalTheory_T_term_integral_near_one_bound
-- name    : GlobalTheory.T.term_integral_near_one_bound
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:48:57.824194+00:00
-- url     : https://prove2.me/theorems/0aaecdff-c482-43ad-9947-c8fffda8d2fb
-- title:
--   T: term integral near one bound
-- statement:
--   The T construction uses the term integral near one bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermIntegralNearOneBoundStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermIntegralNearOneBoundStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermIntegralNearOneBound
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermIntegralNearOneBoundStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.term_integral_near_one_bound : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (J : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → |(cint (S.refU J Λ) (ind fun u => u ∈ S.refU J Λ ∧ S.InZ u)).re * (S.q : ℝ) ^ S.a - 1| ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ (cint (S.refU J Λ) (ind fun u => u ∈ S.refU J Λ ∧ S.InZ u ∧ ¬ S.NoLeak Λ u)).re * (S.q : ℝ) ^ S.a ≤ 16 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ ∀ y : S.V, (∃ u ∈ S.refU J Λ, L.psi0 (S.h y u) ≠ 1) → ‖cint (S.refU J Λ) (fun u => ind (fun u => u ∈ S.refU J Λ ∧ S.InZ u) u * L.psi0 (S.h y u))‖ * (S.q : ℝ) ^ S.a ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by sorry
