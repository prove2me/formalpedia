-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_mem_of_bdd
-- name    : GroundTheory.Automorphic.Spherical.mem_of_bdd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:08.142511+00:00
-- url     : https://prove2.me/theorems/b372caac-084d-52f1-8f06-c61bbd71e8e1
-- title:
--   Spherical: mem of bdd
-- statement:
--   The Spherical construction uses the mem of bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L69-L71

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

theorem GroundTheory.Automorphic.Spherical.mem_of_bdd {x : F} (h : Bdd F 0 x) : x ∈ 𝒪[F] := by sorry
