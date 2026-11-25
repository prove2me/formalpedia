-- Prove2me | Theorems.Thm_GlobalTheory_HL_FrameChange_tri_coeffs
-- name    : GlobalTheory.HL.FrameChange.tri_coeffs
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:33:16.770374+00:00
-- url     : https://prove2.me/theorems/433c59a1-827c-4ac4-bdaf-3a45da420c0a
-- title:
--   Frame Change: tri coeffs
-- statement:
--   The Frame Change construction uses the tri coeffs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermFramesCongrModThetaUnitriangular.lean#L62-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermFramesCongrModThetaUnitriangular.lean#L62-L112

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermFramesCongrModThetaUnitriangular
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameChange
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem GlobalTheory.HL.FrameChange.tri_coeffs {g : Fin (r + 1) → S.V} (hg : ∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0)
    (hli : LinearIndependent E g) {n : S.GLV} (hn : n ∈ S.Nof g) {Λ : Submodule L.O S.V}
    (t : ∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo g j) ↔
      x ∈ Submodule.span L.O ((fun b => n (g b)) '' {i | (i : ℕ) < j}))
    (z : Fin (r + 1) → S.V) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hB0 : ∀ a b, b < a → B a b = 0) (hB1 : ∀ a, B a a = 1) (hz : ∀ b, z b = ∑ a, B a b • g a)
    (hzΛ : ∀ b, z b ∈ Λ) :
    ∃ C : Matrix (Fin (r + 1)) (Fin (r + 1)) L.O, (∀ a b, b < a → C a b = 0) ∧ (∀ a, C a a = 1) ∧
      ∀ b, z b = ∑ a, ((C a b : L.O) : E) • n (g a) := by sorry
