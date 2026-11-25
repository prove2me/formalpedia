-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_ncard_extend_prim_one
-- name    : GlobalTheory.GramCount.ncard_extend_prim_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:28:33.288854+00:00
-- url     : https://prove2.me/theorems/f2ce9b37-d4b5-44e6-9e15-e93a7ee2362a
-- title:
--   Gram Count: ncard extend prim one
-- statement:
--   The Gram Count construction uses the ncard extend prim one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardPrimitiveTupleExtensionsLe.lean#L13-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardPrimitiveTupleExtensionsLe.lean#L13-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPrimitiveAddCharInvolutionInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardDependentVectorsAffineGramLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrimitiveTupleOfLinearIndependentFiniteRingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianQuadricAffineSubspaceResidueRingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardPrimitiveTupleExtensionsLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
open GlobalTheory GlobalTheory.GramCount

theorem GlobalTheory.GramCount.ncard_extend_prim_one : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (k n : ℕ), 2 * k + 1 ≤ n → ∀ (x : Fin k → Fin n → B), Prim c x → ∀ (g : Fin k → B) (t : B), c t = t → |(Set.ncard {y : Fin n → B | Prim c (Fin.cons y x : Fin (k + 1) → Fin n → B) ∧ (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} : ℝ) - (q : ℝ) ^ (2 * n - (2 * k + 1))| ≤ 3 * (q : ℝ) ^ n := by sorry
