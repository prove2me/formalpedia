-- Prove2me | Theorems.Thm_GlobalTheory_HL_WitIndep_witness_independence
-- name    : GlobalTheory.HL.WitIndep.witness_independence
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:06:56.254346+00:00
-- url     : https://prove2.me/theorems/649b2126-d4c1-4270-9167-7b9ce274e88a
-- title:
--   Wit Indep: witness independence
-- statement:
--   The Wit Indep construction uses the witness independence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermInvariantsIndependentOfWitnesses.lean#L239-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermInvariantsIndependentOfWitnesses.lean#L239-L252

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.WitIndep
open GlobalTheory.HL.Eichler

theorem GlobalTheory.HL.WitIndep.witness_independence : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ d Λ n n', S.IsTermW d Λ n n' → S.om d Λ = S.psi n * (S.psi' n')⁻¹ ∧ S.M d Λ = S.Mof (fun b => n (S.f b)) (fun b => n' (S.f' b)) ∧ S.Fr d Λ = S.frameCls (fun b => n (S.f b)) (fun b => n' (S.f' b)) ∧ (∀ y, S.lev (S.fr d Λ) (S.fr' d Λ) y = S.lev (fun b => n (S.f b)) (fun b => n' (S.f' b)) y) ∧ ‖S.om d Λ‖ = 1 := by sorry
