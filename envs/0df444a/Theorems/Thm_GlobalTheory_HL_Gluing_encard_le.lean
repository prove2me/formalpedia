-- Prove2me | Theorems.Thm_GlobalTheory_HL_Gluing_encard_le
-- name    : GlobalTheory.HL.Gluing.encard_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:34:49.221308+00:00
-- url     : https://prove2.me/theorems/f2fb618d-794c-547a-a73f-f8f429f1dbf9
-- title:
--   Gluing: encard le
-- statement:
--   The Gluing construction uses the encard le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/GluingCount.lean#L26-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/GluingCount.lean#L26-L108

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeGramDetAndMinorsOrbitInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardDiscriminantModuleIntegralOverlatticeSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GluingCount
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Gluing
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.HL.Gluing.encard_le [IsNonarchimedeanLocalField F] [CharZero F] {L : LocE F E} {n : ℕ}
    {Hm : Matrix (Fin n) (Fin n) E} (h : IsHermND L Hm) {m : ℕ} {y : Fin m → Fin n → E}
    (hy : LinearIndependent E y) {Y : Submodule E (Fin n → E)}
    (hY : Submodule.span E (Set.range y) = Y) (hc : Y ⊔ perp L Hm Y = ⊤)
    (Mh Λ₀ Md : Submodule L.O (Fin n → E))
    (hMd : ∀ x, x ∈ Md ↔ x ∈ Y ∧ ∀ z ∈ Mh, hf L Hm x z ∈ L.O)
    {ι : Type} [Fintype ι] (b : ι → Fin n → E) (hb : Md = Submodule.span L.O (Set.range b))
    (hN : Mh.toAddSubgroup.relIndex Md.toAddSubgroup ≠ 0) :
    {Λ : Submodule L.O (Fin n → E) | IsSD L Hm Λ ∧ Λ ⊓ Y.restrictScalars L.O = Mh ∧
      Λ ⊓ (perp L Hm Y).restrictScalars L.O = Λ₀}.encard ≤
      ((Mh.toAddSubgroup.relIndex Md.toAddSubgroup ^ Fintype.card ι : ℕ) : ℕ∞) := by sorry
