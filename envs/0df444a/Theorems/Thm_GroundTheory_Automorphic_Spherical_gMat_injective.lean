-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_gMat_injective
-- name    : GroundTheory.Automorphic.Spherical.gMat_injective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:33:49.654163+00:00
-- url     : https://prove2.me/theorems/b07f61a1-0205-5b85-82ec-f214092d97e2
-- title:
--   Spherical: g Mat injective
-- statement:
--   The Spherical construction uses the g Mat injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L222-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L222-L267

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

theorem GroundTheory.Automorphic.Spherical.gMat_injective (S : Finset (Fin n)) :
    Function.Injective fun c : Pairs S → 𝓀[F] =>
      (QuotientGroup.mk (gMat S c) : GL (Fin n) F ⧸ integralGL F n) := by sorry
