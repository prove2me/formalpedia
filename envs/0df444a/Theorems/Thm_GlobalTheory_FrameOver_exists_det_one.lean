-- Prove2me | Theorems.Thm_GlobalTheory_FrameOver_exists_det_one
-- name    : GlobalTheory.FrameOver.exists_det_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:40:11.103008+00:00
-- url     : https://prove2.me/theorems/f0d32394-8a19-483c-9363-7d98bdc5fb72
-- title:
--   Frame Over: exists det one
-- statement:
--   The Frame Over construction uses the exists det one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LatticeCountBoundFrames.lean#L263-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LatticeCountBoundFrames.lean#L263-L284

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

theorem GlobalTheory.FrameOver.exists_det_one [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) {r k : ℕ}
    (S : Frames L r k) {C : Set S.FrP} (hC : S.IsCls C) {p : S.FrP} (hp : p ∈ C) :
    ∃ U U' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, U.det = 1 ∧ U'.det = 1 ∧
      (∀ j, p.1 j = ∑ i, U i j • S.f i) ∧ ∀ j, p.2 j = ∑ i, U' i j • S.f' i := by sorry
