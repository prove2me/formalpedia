-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_mem_integralGL_of_forall_mem
-- name    : GroundTheory.Automorphic.Spherical.mem_integralGL_of_forall_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:34:07.861175+00:00
-- url     : https://prove2.me/theorems/ec8df52a-eb28-58e4-a3c3-f4a05f751d01
-- title:
--   Spherical: mem integral GL of forall mem
-- statement:
--   The Spherical construction uses the mem integral GL of forall mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L19-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L19-L38

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

theorem GroundTheory.Automorphic.Spherical.mem_integralGL_of_forall_mem {g : GL (Fin n) F} (h₁ : ∀ i j, g i j ∈ 𝒪[F])
    (h₂ : valuation F (g : Matrix (Fin n) (Fin n) F).det = 1) : g ∈ integralGL F n := by sorry
