-- Prove2me | Theorems.Thm_GlobalTheory_Sloc_CloseConj_main
-- name    : GlobalTheory.Sloc.CloseConj.main
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:31:50.763675+00:00
-- url     : https://prove2.me/theorems/2d72c694-2a43-5c5d-8d55-35dbf4de5e4c
-- title:
--   Close Conj: main
-- statement:
--   The Close Conj construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PairingConjInverseAdjointCloseToOne.lean#L42-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PairingConjInverseAdjointCloseToOne.lean#L42-L59

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PairingConjInverseAdjointCloseToOne
import Theorems.Thm_GlobalTheory_FrameBasic_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.Sloc GlobalTheory.Sloc.CloseConj
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.Sloc.CloseConj.main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (n : ℕ) (Z Zi M Mi M' : Matrix (Fin n) (Fin n) E) (t e : E), t ∈ L.O → L.cj t = t → Zi * Z = 1 → (∀ i j, e * Z i j ∈ L.O) → (∀ i j, e * Zi i j ∈ L.O) → Mi * M = 1 → M * Mi = 1 → (∀ i j, ∃ o ∈ L.O, (Mi - 1) i j = t * o) → cT L M * Z * M' = Z → ∀ i j, ∃ o ∈ L.O, e * e * (M' - 1) i j = t * o := by sorry
