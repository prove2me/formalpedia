-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_residueLift_sub_mem
-- name    : GroundTheory.Automorphic.Spherical.residueLift_sub_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:34:06.691949+00:00
-- url     : https://prove2.me/theorems/cae04a41-4df8-5464-b20f-6a03693605db
-- title:
--   Spherical: residue Lift sub mem
-- statement:
--   The Spherical construction uses the residue Lift sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L274-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L274-L276

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

theorem GroundTheory.Automorphic.Spherical.residueLift_sub_mem (y : 𝒪[F]) :
    residueLift F (IsLocalRing.residue 𝒪[F] y) - y ∈ IsLocalRing.maximalIdeal 𝒪[F] := by sorry
