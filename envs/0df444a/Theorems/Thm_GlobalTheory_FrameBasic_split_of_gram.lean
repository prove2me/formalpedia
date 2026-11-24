-- Prove2me | Theorems.Thm_GlobalTheory_FrameBasic_split_of_gram
-- name    : GlobalTheory.FrameBasic.split_of_gram
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:37:05.87205+00:00
-- url     : https://prove2.me/theorems/3c4997ce-2afc-43fd-840c-deb496bef3e3
-- title:
--   Frame Basic: split of gram
-- statement:
--   The Frame Basic construction uses the split of gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BasisOfIsCompl.lean#L212-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BasisOfIsCompl.lean#L212-L254

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
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
open scoped Pointwise ENNReal Classical TensorProduct
open GlobalTheory GlobalTheory.FrameBasic
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.FrameBasic.split_of_gram (L : LocE F E) [IsArtinianRing E] {n : ℕ} {H : Matrix (Fin n) (Fin n) E}
    (h : IsHerm L H) {ι : Type} [Fintype ι] (g : ι → Fin n → E)
    (hg : ∀ α : ι → E, (∀ j, ∑ i, α i * hf L H (g i) (g j) = 0) → α = 0) :
    LinearIndependent E g ∧
      IsCompl (Submodule.span E (Set.range g)) (perp L H (Submodule.span E (Set.range g))) := by sorry
