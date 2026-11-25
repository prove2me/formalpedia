-- Prove2me | Theorems.Thm_GlobalTheory_HL_FrameStab_mem_Nof
-- name    : GlobalTheory.HL.FrameStab.mem_Nof
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:30:18.603045+00:00
-- url     : https://prove2.me/theorems/2a564af6-500a-4175-91e0-342a6b35c0e4
-- title:
--   Frame Stab: mem Nof
-- statement:
--   The Frame Stab construction uses the mem Nof property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramesCommonStabiliserEqPairingMatrixStabiliser.lean#L123-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramesCommonStabiliserEqPairingMatrixStabiliser.lean#L123-L163

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameStab
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem GlobalTheory.HL.FrameStab.mem_Nof [IsArtinianRing E] (g g' : Fin (r + 1) → S.V) (T : Fˣ)
    (gram : ∀ a b, hf L S.Hm (g a) (g b) =
      if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E T else 0)
    (W : Submodule E S.V) (hW : ∀ w ∈ W, ∀ y ∈ S.spanTo g (r + 1), hf L S.Hm w y = 0)
    (htop : (S.spanTo g (r + 1) ⊔ S.spanTo g' (r + 1)) ⊔ W = ⊤)
    (hnd : ∀ u ∈ S.spanTo g' (r + 1), (∀ y ∈ S.spanTo g (r + 1), hf L S.Hm u y = 0) → u = 0)
    (s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hs : (∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1))
    (hs' : (∀ i j, j < i → s' i j = 0) ∧ (∀ i, s' i i = 1))
    (h : S.GLV) (hi : h ∈ isomG L S.Hm) (hg : ∀ j, h (g j) = ∑ i, s i j • g i)
    (hg' : ∀ j, h (g' j) = ∑ i, s' i j • g' i) (hw : ∀ w ∈ W, h w = w) : h ∈ S.Nof g := by sorry
