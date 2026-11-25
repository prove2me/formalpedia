-- Prove2me | Theorems.Thm_GlobalTheory_HL_PrimTerm_mem_span_of_mem_Mof
-- name    : GlobalTheory.HL.PrimTerm.mem_span_of_mem_Mof
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:36:20.822092+00:00
-- url     : https://prove2.me/theorems/36dfbe3c-2d30-5fd0-9f53-b285f36a9003
-- title:
--   Prim Term: mem span of mem Mof
-- statement:
--   The Prim Term construction uses the mem span of mem Mof property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemSpanOfMemMof.lean#L61-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemSpanOfMemMof.lean#L61-L89

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualLatticeUnipotentTranslateStandard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanOfMemMof
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PrimTerm
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem GlobalTheory.HL.PrimTerm.mem_span_of_mem_Mof (P P' : Submodule E S.V) (hd : Disjoint P P')
    (g g' : Fin (r + 1) → S.V) (hg : ∀ b, g b ∈ P) (hg' : ∀ b, g' b ∈ P')
    (hi : LinearIndependent E g') (x : S.V) (hx : x ∈ S.Mof g g') (hP : x ∈ P) :
    x ∈ Submodule.span L.O (Set.range g) := by sorry
