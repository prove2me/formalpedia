-- Prove2me | Theorems.Thm_GlobalTheory_HL_ComplAct_graph_mem
-- name    : GlobalTheory.HL.ComplAct.graph_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:29:13.608336+00:00
-- url     : https://prove2.me/theorems/f541cbe1-0c89-5912-b5c2-c3132e8a0122
-- title:
--   Compl Act: graph mem
-- statement:
--   The Compl Act construction uses the graph mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFramesComplementUnitaryActsOnTerms.lean#L151-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFramesComplementUnitaryActsOnTerms.lean#L151-L165

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualLatticeUnipotentTranslateStandardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesComplementUnitaryActsOnTerms
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ComplAct
open GlobalTheory.HL.Eichler GlobalTheory.HL.StdLat
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable [IsNonarchimedeanLocalField F] [CharZero F]
omit [IsNonarchimedeanLocalField F] [CharZero F]

theorem GlobalTheory.HL.ComplAct.graph_mem {h : S.GLV} (hh : h ∈ S.H0) {Λ : Submodule L.O S.V} {p : S.V × S.V}
    (hp : p ∈ S.graphOf Λ) : h • p ∈ S.graphOf (h • Λ) := by sorry
