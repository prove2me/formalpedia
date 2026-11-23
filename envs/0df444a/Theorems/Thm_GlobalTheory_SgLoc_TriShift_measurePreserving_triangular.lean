-- Prove2me | Theorems.Thm_GlobalTheory_SgLoc_TriShift_measurePreserving_triangular
-- name    : GlobalTheory.SgLoc.TriShift.measurePreserving_triangular
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:00.478817+00:00
-- url     : https://prove2.me/theorems/88510c0e-b6ea-4a8d-8614-01dbca96a615
-- title:
--   Tri Shift: measure Preserving triangular
-- statement:
--   The Tri Shift construction uses the measure Preserving triangular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingTriangular.lean#L58-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingTriangular.lean#L58-L92

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CokernelPairSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc GlobalTheory.SgLoc
open scoped ComplexOrder
open GlobalTheory GlobalTheory.SgLoc GlobalTheory.SgLoc.TriShift
variable {G : Type} [AddGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  (μ : Measure G) [SigmaFinite μ] [μ.IsAddRightInvariant]
  {ι : Type} [Fintype ι]
open ValuativeRel MeasureTheory ComplexConjugate
open scoped ComplexOrder
variable {G : Type} [AddGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  (μ : Measure G) [SigmaFinite μ] [μ.IsAddRightInvariant]
  {ι : Type} [Fintype ι]

theorem GlobalTheory.SgLoc.TriShift.measurePreserving_triangular (rk : ι → ℕ) (f : ι → (ι → G) → G)
    (hf : ∀ i, Measurable (f i))
    (hd : ∀ i x y, (∀ j, rk j < rk i → x j = y j) → f i x = f i y) :
    MeasurePreserving (fun (x : ι → G) i => x i + f i x) (Measure.pi fun _ : ι => μ)
      (Measure.pi fun _ : ι => μ) := by sorry
