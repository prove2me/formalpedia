-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_infiniteSchwartz_homeomorphMixedSpace
-- name    : GroundTheory.Global.HeckeCharacter.infiniteSchwartz_homeomorphMixedSpace
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:48:33.847233+00:00
-- url     : https://prove2.me/theorems/0349a693-f3a9-5b43-a2cf-c7bdbfbd7224
-- title:
--   Hecke Character: infinite Schwartz homeomorph Mixed Space
-- statement:
--   The Hecke Character construction uses the infinite Schwartz homeomorph Mixed Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsInfinite.lean#L102-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsInfinite.lean#L102-L130

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

theorem GroundTheory.Global.HeckeCharacter.infiniteSchwartz_homeomorphMixedSpace (x : InfiniteAdeleRing K) :
    χ.infiniteSchwartz (homeomorphMixedSpace K x) = ∏ w, χ.infiniteTest w (x w) := by sorry
