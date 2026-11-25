-- Prove2me | Theorems.Thm_GlobalTheory_MatrixIndex_index_rmul
-- name    : GlobalTheory.MatrixIndex.index_rmul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:26.991773+00:00
-- url     : https://prove2.me/theorems/c1761b12-7834-48e5-aa69-ba0253b1ca86
-- title:
--   Matrix Index: index rmul
-- statement:
--   The Matrix Index construction uses the index rmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SpanEqMap.lean#L95-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SpanEqMap.lean#L95-L154

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanEqMap
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
open GlobalTheory GlobalTheory.MatrixIndex
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.MatrixIndex.index_rmul : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n m : ℕ} (y : Fin m → Fin n → E), LinearIndependent E y → ∀ A : Matrix (Fin m) (Fin m) E, IsIntM L A → IsUnit A.det → 0 ≤ vE L ϖ (A.det * L.cj A.det) ∧ (Submodule.span L.O (Set.range (rmul y A))).toAddSubgroup.relIndex (Submodule.span L.O (Set.range y)).toAddSubgroup = resQ ϖ ^ (vE L ϖ (A.det * L.cj A.det)).toNat := by sorry
