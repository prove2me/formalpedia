-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_coe_unipC
-- name    : GroundTheory.Automorphic.Spherical.coe_unipC
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:06.690669+00:00
-- url     : https://prove2.me/theorems/7b80f6f8-019f-502e-8a42-999d6fd07b22
-- title:
--   Spherical: coe unip C
-- statement:
--   The Spherical construction uses the coe unip C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L139-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L139-L140

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

theorem GroundTheory.Automorphic.Spherical.coe_unipC (S : Finset (Fin n)) (c : Pairs S → 𝓀[F]) :
    ((unipC S c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + cMat S c := by sorry
