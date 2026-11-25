-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_prod_zpow_uniformizer
-- name    : GroundTheory.Automorphic.Spherical.prod_zpow_uniformizer
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:33:55.174278+00:00
-- url     : https://prove2.me/theorems/40b04d41-c2bb-4d63-b28a-264c1252856f
-- title:
--   Spherical: prod zpow uniformizer
-- statement:
--   The Spherical construction uses the prod zpow uniformizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L180-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L180-L187

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

theorem GroundTheory.Automorphic.Spherical.prod_zpow_uniformizer {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, (uniformizer F : F) ^ f i = (uniformizer F : F) ^ ∑ i ∈ s, f i := by sorry
