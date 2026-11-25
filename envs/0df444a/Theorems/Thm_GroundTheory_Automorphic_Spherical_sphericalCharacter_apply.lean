-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_sphericalCharacter_apply
-- name    : GroundTheory.Automorphic.Spherical.sphericalCharacter_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:44:39.058149+00:00
-- url     : https://prove2.me/theorems/4d292492-2357-4801-bf8c-d20a7a86cfd5
-- title:
--   Spherical: spherical Character apply
-- statement:
--   The Spherical construction uses the spherical Character apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalPrincipal.lean#L242-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalPrincipal.lean#L242-L243

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
variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem GroundTheory.Automorphic.Spherical.sphericalCharacter_apply (hχ : IsUnramified χ) (h : SphericalHecke μ (F := F) (n := n)) :
    sphericalCharacter μ hχ h = sphericalEigen χ μ h := by sorry
