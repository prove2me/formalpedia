-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_integral_infiniteSchwartz
-- name    : GroundTheory.Global.HeckeCharacter.integral_infiniteSchwartz
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:56:36.314899+00:00
-- url     : https://prove2.me/theorems/c92ab393-26f5-585c-bf8a-8af981cc1387
-- title:
--   Hecke Character: integral infinite Schwartz
-- statement:
--   The Hecke Character construction uses the integral infinite Schwartz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsInfinite.lean#L146-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsInfinite.lean#L146-L176

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

theorem GroundTheory.Global.HeckeCharacter.integral_infiniteSchwartz {s : ℂ} (hs : 0 < s.re) :
    ∫ a : (InfiniteAdeleRing K)ˣ, χ.infiniteSchwartz (homeomorphMixedSpace K a) *
      (χ.toIdele (IdeleGroup.ofInfinite a) : ℂ) *
        ((∏ w, ‖(a : InfiniteAdeleRing K) w‖ ^ w.mult : ℝ) : ℂ) ^ s ∂infiniteIdeleMeasure K =
      ∏ w, infiniteConst w * χ.infiniteGamma w s := by sorry
