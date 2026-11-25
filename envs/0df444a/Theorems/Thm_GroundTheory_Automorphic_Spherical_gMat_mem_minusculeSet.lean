-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_gMat_mem_minusculeSet
-- name    : GroundTheory.Automorphic.Spherical.gMat_mem_minusculeSet
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:08.97785+00:00
-- url     : https://prove2.me/theorems/9973d55a-867d-5002-be57-d9faba0990bc
-- title:
--   Spherical: g Mat mem minuscule Set
-- statement:
--   The Spherical construction uses the g Mat mem minuscule Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L193-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L193-L220

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

theorem GroundTheory.Automorphic.Spherical.gMat_mem_minusculeSet (S : Finset (Fin n)) (c : Pairs S → 𝓀[F]) :
    gMat S c ∈ minusculeSet F n S.card := by sorry
