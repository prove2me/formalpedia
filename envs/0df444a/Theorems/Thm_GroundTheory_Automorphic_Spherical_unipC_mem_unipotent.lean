-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_unipC_mem_unipotent
-- name    : GroundTheory.Automorphic.Spherical.unipC_mem_unipotent
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:36:39.875002+00:00
-- url     : https://prove2.me/theorems/caf517fe-2ef9-48e2-af90-1611d7dbfb53
-- title:
--   Spherical: unip C mem unipotent
-- statement:
--   The Spherical construction uses the unip C mem unipotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L145-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L145-L154

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

theorem GroundTheory.Automorphic.Spherical.unipC_mem_unipotent (S : Finset (Fin n)) (c : Pairs S → 𝓀[F]) :
    unipC S c ∈ unipotent F n := by sorry
