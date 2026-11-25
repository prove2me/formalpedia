-- Prove2me | Theorems.Thm_GlobalTheory_HL_Gluing_main
-- name    : GlobalTheory.HL.Gluing.main
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:55:34.180653+00:00
-- url     : https://prove2.me/theorems/039ed71a-828f-4118-a459-0717a2e1127b
-- title:
--   Gluing: main
-- statement:
--   The Gluing construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsGluingHomomorphismDefectGroup.lean#L283-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsGluingHomomorphismDefectGroup.lean#L283-L299

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ComplementLatticeOfTermFreeRank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsGluingHomomorphismDefectGroup
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_HL_CompLat_main

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Gluing
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} {S : Frames L r k}
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} {S : _root_.GlobalTheory.HL.Frames L r k}

theorem GlobalTheory.HL.Gluing.main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → (∀ w ∈ S.complementLatticeOfDatum d, ∃ y ∈ S.sat Λ, S.TauRel d Λ w y) ∧ (∀ w y y', S.TauRel d Λ w y → (S.TauRel d Λ w y' ↔ y - y' ∈ S.M d Λ)) ∧ (∀ c ∈ L.O, ∀ w₁ w₂ y₁ y₂, S.TauRel d Λ w₁ y₁ → S.TauRel d Λ w₂ y₂ → S.TauRel d Λ (c • w₁ + w₂) (c • y₁ + y₂)) ∧ (∀ w ∈ S.W0, w ∈ Λ ↔ (w ∈ S.complementLatticeOfDatum d ∧ S.TauRel d Λ w 0)) ∧ S.Ihat d Λ ≤ S.sat Λ ∧ ∃ b : Fin (k - 1) → S.V, LinearIndependent E b ∧ S.complementLatticeOfDatum d = (Submodule.span L.O (Set.range b) : Set S.V) := by sorry
