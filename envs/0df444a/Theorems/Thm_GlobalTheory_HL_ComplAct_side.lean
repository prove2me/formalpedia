-- Prove2me | Theorems.Thm_GlobalTheory_HL_ComplAct_side
-- name    : GlobalTheory.HL.ComplAct.side
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:31:26.903802+00:00
-- url     : https://prove2.me/theorems/07fb21d3-6d84-5aa0-b28a-3cd0dd7e193f
-- title:
--   Compl Act: side
-- statement:
--   The Compl Act construction uses the side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFramesComplementUnitaryActsOnTerms.lean#L100-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFramesComplementUnitaryActsOnTerms.lean#L100-L144

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

theorem GlobalTheory.HL.ComplAct.side {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (hg : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) {A : Submodule L.O S.V}
    (hA : S.IsInner g gs A) {n : S.GLV} (hn : n ∈ S.Nof g) {h : S.GLV} (hh : h ∈ isomG L S.Hm)
    (hfix : ∀ x ∈ S.spanTo g (r + 1), h x = x) :
    S.IsInner g gs (h • A) ∧ ∃ m ∈ S.Nof g, (∀ b, m (g b) = n (g b)) ∧
      h • n • S.stdLat g gs A = m • S.stdLat g gs (h • A) := by sorry
