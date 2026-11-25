-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_gMat_inv_apply
-- name    : GroundTheory.Automorphic.Spherical.gMat_inv_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:33:57.212398+00:00
-- url     : https://prove2.me/theorems/7eba2faa-3bf5-567b-9041-da1a5011704a
-- title:
--   Spherical: g Mat inv apply
-- statement:
--   The Spherical construction uses the g Mat inv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L171-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L171-L177

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

theorem GroundTheory.Automorphic.Spherical.gMat_inv_apply (S : Finset (Fin n)) (c : Pairs S → 𝓀[F]) (i j : Fin n) :
    ((gMat S c)⁻¹ : GL (Fin n) F) i j = π ^ (-lamS S i) *
      ((1 : Matrix (Fin n) (Fin n) F) i j - cMat S c i j) := by sorry
