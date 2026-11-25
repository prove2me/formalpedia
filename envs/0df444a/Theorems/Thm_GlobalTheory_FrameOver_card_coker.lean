-- Prove2me | Theorems.Thm_GlobalTheory_FrameOver_card_coker
-- name    : GlobalTheory.FrameOver.card_coker
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:27:35.355333+00:00
-- url     : https://prove2.me/theorems/30675f6e-dc32-509a-8604-0c3f2e8981e8
-- title:
--   Frame Over: card coker
-- statement:
--   The Frame Over construction uses the card coker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LatticeCountBoundFrames.lean#L103-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LatticeCountBoundFrames.lean#L103-L154

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSubmoduleAndHomLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeCountBoundFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FrameOver
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.FrameOver.card_coker [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) {ϖ : 𝒪[F]}
    (hϖ : Irreducible ϖ) {ι : Type} [Fintype ι] [DecidableEq ι] (N : Matrix ι ι L.O) (a : ℕ)
    (u : (𝒪[F])ˣ) (hN : ((N.det : L.O) : E) = algebraMap F E ((ϖ : F) ^ a * ((u : 𝒪[F]) : F))) :
    Nat.card ((ι → L.O) ⧸ LinearMap.range N.vecMulLinear) = resQ ϖ ^ (2 * a) := by sorry
