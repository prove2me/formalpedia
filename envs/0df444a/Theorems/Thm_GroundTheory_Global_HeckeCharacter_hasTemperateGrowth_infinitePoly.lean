-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_hasTemperateGrowth_infinitePoly
-- name    : GroundTheory.Global.HeckeCharacter.hasTemperateGrowth_infinitePoly
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:49:13.995412+00:00
-- url     : https://prove2.me/theorems/c2184e20-d0f9-4ff3-a492-91482fafa873
-- title:
--   Hecke Character: has Temperate Growth infinite Poly
-- statement:
--   The Hecke Character construction uses the has Temperate Growth infinite Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsInfinite.lean#L65-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsInfinite.lean#L65-L88

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

theorem GroundTheory.Global.HeckeCharacter.hasTemperateGrowth_infinitePoly : χ.infinitePoly.HasTemperateGrowth := by sorry
