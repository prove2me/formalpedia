-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_MBdd_mul
-- name    : GroundTheory.Automorphic.Spherical.MBdd.mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:08:19.164514+00:00
-- url     : https://prove2.me/theorems/5a0f43f8-fb48-52a1-bd40-1fc508a02b06
-- title:
--   MBdd: mul
-- statement:
--   The MBdd construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L44-L47

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalMinuscule
import Theorems.Thm_GroundTheory_Automorphic_Spherical_Bdd_mul

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

theorem GroundTheory.Automorphic.Spherical.MBdd.mul {s t : ℤ} {A B : Matrix (Fin n) (Fin n) F} (hA : MBdd F s A) (hB : MBdd F t B) :
    MBdd F (s + t) (A * B) := by sorry
