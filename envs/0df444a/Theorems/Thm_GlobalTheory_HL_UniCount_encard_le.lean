-- Prove2me | Theorems.Thm_GlobalTheory_HL_UniCount_encard_le
-- name    : GlobalTheory.HL.UniCount.encard_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:34:29.459842+00:00
-- url     : https://prove2.me/theorems/b16c6416-feea-417f-9030-eaf92b855c23
-- title:
--   Uni Count: encard le
-- statement:
--   The Uni Count construction uses the encard le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardUniCosetsLe.lean#L124-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardUniCosetsLe.lean#L124-L173

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardQuotEqPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUniCosetsLe
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.UniCount
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {N : ℕ}

theorem GlobalTheory.HL.UniCount.encard_le (L : LocE F E) (δ : L.O) (hδ : IsUnit (δ : E))
    [Finite (L.O ⧸ Ideal.span {δ})] (N : ℕ) :
    {C : Set (Matrix (Fin N) (Fin N) E) | ∃ u, IsUni u ∧ (∀ i j, (δ : E) * u i j ∈ L.O) ∧
      C = cos L u}.encard ≤
      ((Nat.card (L.O ⧸ Ideal.span {δ}) ^ (N * (N - 1) / 2) : ℕ) : ℕ∞) := by sorry
