-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_zpow_mem_of_nonneg
-- name    : GroundTheory.Automorphic.Spherical.zpow_mem_of_nonneg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:33:55.041821+00:00
-- url     : https://prove2.me/theorems/ceb9b43f-f3d3-5867-a39c-372f7a119fd1
-- title:
--   Spherical: zpow mem of nonneg
-- statement:
--   The Spherical construction uses the zpow mem of nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L188-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L188-L191

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

theorem GroundTheory.Automorphic.Spherical.zpow_mem_of_nonneg {t : ℤ} (ht : 0 ≤ t) : π ^ t ∈ 𝒪[F] := by sorry
