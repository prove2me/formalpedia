-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_diag_mul_torusPow
-- name    : GroundTheory.Automorphic.Spherical.diag_mul_torusPow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:09.483503+00:00
-- url     : https://prove2.me/theorems/29adf8b5-69c2-54c9-b035-94cdf114350b
-- title:
--   Spherical: diag mul torus Pow
-- statement:
--   The Spherical construction uses the diag mul torus Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L278-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L278-L280

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalMinuscule
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
open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra
open ValuativeRel (valuation)
open scoped ValuativeRel
open GroundTheory.Automorphic.Spherical
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
local notation "π" => (GLnLocal.uniformizer F : F)

theorem GroundTheory.Automorphic.Spherical.diag_mul_torusPow {u : GL (Fin n) F} (hu : u ∈ unipotent F n) (l : Fin n → ℤ) (i j : Fin n) :
    ((u * torusPow F n l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = u i j * π ^ l j := by sorry
