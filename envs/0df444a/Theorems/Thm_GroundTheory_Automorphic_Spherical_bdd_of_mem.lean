-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_bdd_of_mem
-- name    : GroundTheory.Automorphic.Spherical.bdd_of_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:27:36.543545+00:00
-- url     : https://prove2.me/theorems/731bd1ed-a79d-5f88-9ebc-c6fa40822699
-- title:
--   Spherical: bdd of mem
-- statement:
--   The Spherical construction uses the bdd of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L54-L56

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

theorem GroundTheory.Automorphic.Spherical.bdd_of_mem {x : F} (hx : x ∈ 𝒪[F]) : Bdd F 0 x := by sorry
