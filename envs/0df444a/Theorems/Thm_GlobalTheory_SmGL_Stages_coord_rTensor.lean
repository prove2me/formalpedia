-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_Stages_coord_rTensor
-- name    : GlobalTheory.SmGL.Stages.coord_rTensor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:53.926265+00:00
-- url     : https://prove2.me/theorems/df09c10a-e1a2-4569-9b67-bf0fb5ba96be
-- title:
--   Stages: coord r Tensor
-- statement:
--   The Stages construction uses the coord r Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyInv.lean#L73-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyInv.lean#L73-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Topology Filter
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Stages
variable {F G M W X Y Z : Type} [Field F] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group M] [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup W] [Module F W]
  [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y] [AddCommGroup Z] [Module F Z]

theorem GlobalTheory.SmGL.Stages.coord_rTensor {ι : Type} [DecidableEq ι] (b : Module.Basis ι F X) (f : Y →ₗ[F] W) (y : Y ⊗[F] X)
    (i : ι) : TensorProduct.equivFinsuppOfBasisRight b (f.rTensor X y) i =
      f (TensorProduct.equivFinsuppOfBasisRight b y i) := by sorry
