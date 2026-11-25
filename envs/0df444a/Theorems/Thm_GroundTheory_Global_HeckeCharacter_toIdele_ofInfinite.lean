-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_toIdele_ofInfinite
-- name    : GroundTheory.Global.HeckeCharacter.toIdele_ofInfinite
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:45:17.665994+00:00
-- url     : https://prove2.me/theorems/b86e86e7-0b2a-4487-b2d2-74b4a159fa25
-- title:
--   Hecke Character: to Idele of Infinite
-- statement:
--   The Hecke Character construction uses the to Idele of Infinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsInfinite.lean#L132-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsInfinite.lean#L132-L144

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_EulerFactorsArch
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_EulerFactorsInfinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField InfinitePlace InfinitePlace.Completion MeasureTheory Complex ComplexConjugate
  NumberField.mixedEmbedding Function
open scoped Real SchwartzMap Classical RealInnerProductSpace
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.HeckeCharacter
variable (χ : HeckeCharacter K)

theorem GroundTheory.Global.HeckeCharacter.toIdele_ofInfinite (a : (InfiniteAdeleRing K)ˣ) :
    χ.toIdele (IdeleGroup.ofInfinite a) =
      ∏ w, χ.infiniteComponent w (IdeleGroup.infiniteComponent w a) := by sorry
