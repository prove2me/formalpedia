-- Prove2me | Theorems.Thm_GlobalTheory_UnramOrder_proper_ideals
-- name    : GlobalTheory.UnramOrder.proper_ideals
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:51:25.557805+00:00
-- url     : https://prove2.me/theorems/ab8861be-a4e2-4f6d-b2ee-b7db76ccc329
-- title:
--   Unram Order: proper ideals
-- statement:
--   The Unram Order construction uses the proper ideals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ProperIdealsOfHenselian.lean#L286-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ProperIdealsOfHenselian.lean#L286-L304

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ProperIdealsOfHenselian
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
open GlobalTheory GlobalTheory.UnramOrder
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.UnramOrder.proper_ideals : ∀ {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ →
    (∀ I : Ideal L.O, I ≠ ⊤ → ∀ x ∈ I, ∃ c ∈ L.O, (x : E) = algebraMap F E ϖ * c) ∨
    ∃ π ∈ L.O, π * L.cj π = algebraMap F E ϖ ∧ ∀ I : Ideal L.O, I ≠ ⊤ →
      (∀ x ∈ I, ∃ c ∈ L.O, (x : E) = π * c) ∨ ∀ x ∈ I, ∃ c ∈ L.O, (x : E) = L.cj π * c := by sorry
