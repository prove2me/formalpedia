-- Prove2me | Theorems.Thm_GlobalTheory_FrameOver_count
-- name    : GlobalTheory.FrameOver.count
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:27:46.288318+00:00
-- url     : https://prove2.me/theorems/28db01fa-5e4b-5023-a253-41a439e98c82
-- title:
--   Frame Over: count
-- statement:
--   The Frame Over construction uses the count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LatticeCountBoundFrames.lean#L156-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LatticeCountBoundFrames.lean#L156-L222

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSubmoduleAndHomLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeCountBoundFrames
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
open GlobalTheory GlobalTheory.FrameOver
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.FrameOver.count [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) {ϖ : 𝒪[F]}
    (hϖ : Irreducible ϖ) {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V]
    [Module E V] (g : ι → V) (Φ : V →ₗ[E] (ι → E)) (a : ℕ) (u : (𝒪[F])ˣ)
    (hN : (Matrix.of fun i j => Φ (g i) j).det = algebraMap F E ((ϖ : F) ^ a * ((u : 𝒪[F]) : F)))
    (s : Set (Submodule L.O V))
    (hs : ∀ P ∈ s, (∀ i, g i ∈ P) ∧ (∀ x ∈ P, x ∈ Submodule.span E (Set.range g)) ∧
      ∀ x ∈ P, ∀ j, Φ x j ∈ L.O) :
    s.encard ≤ (resQ ϖ ^ (2 * a * Fintype.card ι) : ℕ) := by sorry
