-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_iwasawaExponent_gMat
-- name    : GroundTheory.Automorphic.Spherical.iwasawaExponent_gMat
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:37:07.128037+00:00
-- url     : https://prove2.me/theorems/1f9d175a-31ee-4bca-a7f5-3e95bb1371e0
-- title:
--   Spherical: iwasawa Exponent g Mat
-- statement:
--   The Spherical construction uses the iwasawa Exponent g Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L159-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L159-L162

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

theorem GroundTheory.Automorphic.Spherical.iwasawaExponent_gMat (S : Finset (Fin n)) (c : Pairs S → 𝓀[F]) :
    iwasawaExponent F n (gMat S c) = lamS S := by sorry
