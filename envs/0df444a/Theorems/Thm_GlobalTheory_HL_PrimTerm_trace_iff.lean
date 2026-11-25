-- Prove2me | Theorems.Thm_GlobalTheory_HL_PrimTerm_trace_iff
-- name    : GlobalTheory.HL.PrimTerm.trace_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:36:10.411926+00:00
-- url     : https://prove2.me/theorems/40c4a47d-0416-5c71-8d57-12de1b8e82ad
-- title:
--   Prim Term: trace iff
-- statement:
--   The Prim Term construction uses the trace iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemSpanOfMemMof.lean#L91-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemSpanOfMemMof.lean#L91-L113

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

theorem GlobalTheory.HL.PrimTerm.trace_iff (Λ : Submodule L.O S.V) (f f' g g' : Fin (r + 1) → S.V)
    (hd : Disjoint (Submodule.span E (Set.range f)) (Submodule.span E (Set.range f')))
    (hg : ∀ b, g b ∈ Submodule.span E (Set.range f))
    (hg' : ∀ b, g' b ∈ Submodule.span E (Set.range f'))
    (hi : LinearIndependent E g') (hME : S.spanTo f (r + 1) ≤ S.ME) (hs : S.sat Λ = S.Mof g g')
    (x : S.V) : (x ∈ Λ ∧ x ∈ S.spanTo f (r + 1)) ↔ x ∈ Submodule.span L.O (Set.range fun b => g b) := by sorry
