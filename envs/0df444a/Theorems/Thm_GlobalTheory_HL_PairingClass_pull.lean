-- Prove2me | Theorems.Thm_GlobalTheory_HL_PairingClass_pull
-- name    : GlobalTheory.HL.PairingClass.pull
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:33:00.88575+00:00
-- url     : https://prove2.me/theorems/2afbd180-c4b1-4b19-8a8c-75dc09e60207
-- title:
--   Pairing Class: pull
-- statement:
--   The Pairing Class construction uses the pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermOverRelationUniqueness.lean#L177-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermOverRelationUniqueness.lean#L177-L186

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NotField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermOverRelationUniqueness
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PairingClass
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

theorem GlobalTheory.HL.PairingClass.pull {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S) (g : V ≃ₗ[E] V)
    (f : Fin (r + 1) → V) (f₁ : Fin (r + 1) → S.V) (hf : ∀ a, f₁ a = c.e (f a))
    (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (h : ∀ j, c.grp g (f₁ j) = ∑ i, s i j • f₁ i) :
    (fun j => g (f j)) = act f s := by sorry
