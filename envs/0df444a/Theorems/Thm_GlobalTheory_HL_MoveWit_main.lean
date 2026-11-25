-- Prove2me | Theorems.Thm_GlobalTheory_HL_MoveWit_main
-- name    : GlobalTheory.HL.MoveWit.main
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:05:54.060129+00:00
-- url     : https://prove2.me/theorems/2b209c71-5c6d-4114-8ca2-0ed95a2a3935
-- title:
--   Move Wit: main
-- statement:
--   The Move Wit construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MoveLatticeIsTermSameDatumWithWitnesses.lean#L191-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MoveLatticeIsTermSameDatumWithWitnesses.lean#L191-L262

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfSameTrace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerMapMemUnipotentCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesDatumMovePropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MoveLatticeIsTermSameDatumWithWitnesses
import Theorems.Thm_GlobalTheory_CommonDenominator_main
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_FrameLevel_main
import Theorems.Thm_GlobalTheory_LengthDualFunctional_main
import Theorems.Thm_GlobalTheory_LengthQuotientSpanValuation_main

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MoveWit
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem GlobalTheory.HL.MoveWit.main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → ∃ n₀ ∈ S.N, ∃ n₀' ∈ S.N', ∃ n'' ∈ S.N', (∀ v, n₀ v = eich L S.Hm x u s v) ∧ (∀ v, n₀⁻¹ v = eich L S.Hm x (-u) (L.cj s) v) ∧ (∀ v, n₀' v = eich L S.Hm x' u s v) ∧ (∀ v ∈ perp L S.Hm S.X', n'' v = v) ∧ ((n₀⁻¹ • Λ : Submodule L.O S.V) : Set S.V) = S.moved Λ x u s ∧ S.IsTermW d (n₀⁻¹ • Λ) (n₀⁻¹ * (S.wit d Λ).1) (n'' * n₀' * (S.wit d Λ).2) := by sorry
