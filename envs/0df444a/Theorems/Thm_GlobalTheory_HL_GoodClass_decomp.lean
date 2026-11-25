-- Prove2me | Theorems.Thm_GlobalTheory_HL_GoodClass_decomp
-- name    : GlobalTheory.HL.GoodClass.decomp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:43:28.828673+00:00
-- url     : https://prove2.me/theorems/e35a0c32-a3a2-4f0b-9c20-2b54362b5adf
-- title:
--   Good Class: decomp
-- statement:
--   The Good Class construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/UnitEntries.lean#L81-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/UnitEntries.lean#L81-L176

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitEntries
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GoodClass
variable {E : Type} [CommRing E] {n : ℕ}

theorem GlobalTheory.HL.GoodClass.decomp (O : Subring E) (W : Matrix (Fin n) (Fin n) E) (σ : Fin n → Fin n)
    (hσ : ∀ a, σ (σ a) = a) (hmono : ∀ a b : Fin n, a ≤ b → (a : ℕ) + σ a ≤ b + σ b)
    (h0 : ∀ a b, b ≠ σ a → W a b = 0) (hu : ∀ a, UnitIn O (W a (σ a)))
    (L U : Matrix (Fin n) (Fin n) E) (hL : UpU L.transpose) (hU : UpU U)
    (hZ : ∀ i j, (L * W * U) i j ∈ O) :
    ∃ D L₁ V U₁ : Matrix (Fin n) (Fin n) E, UpU D.transpose ∧ UpU L₁.transpose ∧ UpU V ∧ UpU U₁ ∧
      (∀ i j, L₁ i j ∈ O) ∧ (∀ i j, U₁ i j ∈ O) ∧ L = L₁ * D ∧ U = V * U₁ ∧ D * W * V = W := by sorry
