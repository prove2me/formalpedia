-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_Bdd_add
-- name    : GroundTheory.Automorphic.Spherical.Bdd.add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:27:30.298859+00:00
-- url     : https://prove2.me/theorems/960f67a9-4e06-5241-94da-d13ecb558498
-- title:
--   Bdd: add
-- statement:
--   The Bdd construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L26-L27

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

theorem GroundTheory.Automorphic.Spherical.Bdd.add {t : ℤ} {x y : F} (hx : Bdd F t x) (hy : Bdd F t y) : Bdd F t (x + y) := by sorry
