-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_valuation_det_eq_one
-- name    : GroundTheory.Automorphic.Spherical.valuation_det_eq_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:36:24.835172+00:00
-- url     : https://prove2.me/theorems/aeba90a2-1440-4ff5-a570-ee0067821d07
-- title:
--   Spherical: valuation det eq one
-- statement:
--   The Spherical construction uses the valuation det eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L225-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L225-L232

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

theorem GroundTheory.Automorphic.Spherical.valuation_det_eq_one {k : GL (Fin n) F} (hk : k ∈ integralGL F n) :
    valuation F (k : Matrix (Fin n) (Fin n) F).det = 1 := by sorry
