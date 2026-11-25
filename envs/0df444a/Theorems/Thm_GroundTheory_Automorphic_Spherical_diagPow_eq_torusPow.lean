-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_diagPow_eq_torusPow
-- name    : GroundTheory.Automorphic.Spherical.diagPow_eq_torusPow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:27:27.653913+00:00
-- url     : https://prove2.me/theorems/fc4a8fba-ef03-5aed-8236-2d77807e8cff
-- title:
--   Spherical: diag Pow eq torus Pow
-- statement:
--   The Spherical construction uses the diag Pow eq torus Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L206-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L206-L207

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalSatake
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular
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
open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra ValuativeRel
open scoped ValuativeRel
open GroundTheory.Automorphic.Spherical
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem GroundTheory.Automorphic.Spherical.diagPow_eq_torusPow (μ : Fin n → ℤ) : Cartan.diagPow F n μ = torusPow F n μ := by sorry
