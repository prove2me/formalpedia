-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_mul_mem_minusculeSet
-- name    : GroundTheory.Automorphic.Spherical.mul_mem_minusculeSet
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:35:55.744785+00:00
-- url     : https://prove2.me/theorems/5999b936-9230-44a1-b837-3a8d9d027580
-- title:
--   Spherical: mul mem minuscule Set
-- statement:
--   The Spherical construction uses the mul mem minuscule Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L73-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L73-L91

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

theorem GroundTheory.Automorphic.Spherical.mul_mem_minusculeSet {k : ℕ} {g a b : GL (Fin n) F} (hg : g ∈ minusculeSet F n k)
    (ha : a ∈ integralGL F n) (hb : b ∈ integralGL F n) : a * g * b ∈ minusculeSet F n k := by sorry
