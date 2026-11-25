-- Prove2me | Theorems.Thm_GlobalTheory_UnramOrder_card_coker_of_det_eq
-- name    : GlobalTheory.UnramOrder.card_coker_of_det_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:13:34.059141+00:00
-- url     : https://prove2.me/theorems/71c047a4-d90a-4a50-b254-966e81321ce8
-- title:
--   Unram Order: card coker of det eq
-- statement:
--   The Unram Order construction uses the card coker of det eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardCokernelUnramifiedOrderMatrixOfDetBase.lean#L120-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardCokernelUnramifiedOrderMatrixOfDetBase.lean#L120-L207

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardCokernelUnramifiedOrderMatrixOfDetBase
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

theorem GlobalTheory.UnramOrder.card_coker_of_det_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι L.O) (j : ℕ) (u : (𝒪[F])ˣ), ((A.det : L.O) : E) = algebraMap F E ((ϖ : F) ^ j * ((u : 𝒪[F]) : F)) → Nat.card ((ι → L.O) ⧸ LinearMap.range A.mulVecLin) = _root_.GlobalTheory.HL.resQ ϖ ^ (2 * j) := by sorry
