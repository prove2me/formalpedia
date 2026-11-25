-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_fixedVectors_eq_span
-- name    : GroundTheory.Automorphic.Spherical.fixedVectors_eq_span
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:43:35.523524+00:00
-- url     : https://prove2.me/theorems/cafda360-f2fd-5604-9214-a15383d46928
-- title:
--   Spherical: fixed Vectors eq span
-- statement:
--   The Spherical construction uses the fixed Vectors eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalPrincipal.lean#L178-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalPrincipal.lean#L178-L184

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalCommutative
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalPrincipal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Matrix GLnLocal Iwasawa Parabolic HeckeAlgebra
open scoped ValuativeRel
open GroundTheory.Automorphic.Spherical
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {χ : levi F n (id : Fin n → Fin n) →* ℂ}

theorem GroundTheory.Automorphic.Spherical.fixedVectors_eq_span (hχ : IsUnramified χ) :
    fixedVectors (principalSeries F n χ) (integralGL F n) = ℂ ∙ sphericalVector hχ := by sorry
