-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_apply_out
-- name    : GroundTheory.Automorphic.Spherical.apply_out
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:27:20.59884+00:00
-- url     : https://prove2.me/theorems/5bae7efe-3e91-5e7b-b730-19c0fee78ee7
-- title:
--   Spherical: apply out
-- statement:
--   The Spherical construction uses the apply out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L316-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L316-L320

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
variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem GroundTheory.Automorphic.Spherical.apply_out (h : SphericalHecke μ (F := F) (n := n)) (g : GL (Fin n) F) :
    (h : HeckeAlgebra μ) (QuotientGroup.mk g : GL (Fin n) F ⧸ integralGL F n).out =
      (h : HeckeAlgebra μ) g := by sorry
