-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_cMat_mem
-- name    : GroundTheory.Automorphic.Spherical.cMat_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:33:51.018484+00:00
-- url     : https://prove2.me/theorems/8d6361ae-6ec6-59d4-b6f4-ee85596ee895
-- title:
--   Spherical: c Mat mem
-- statement:
--   The Spherical construction uses the c Mat mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L119-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L119-L123

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

theorem GroundTheory.Automorphic.Spherical.cMat_mem {S : Finset (Fin n)} (c : Pairs S → 𝓀[F]) (i j : Fin n) : cMat S c i j ∈ 𝒪[F] := by sorry
