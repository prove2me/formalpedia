-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_satake_coeff
-- name    : GroundTheory.Automorphic.Spherical.satake_coeff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:30:57.576484+00:00
-- url     : https://prove2.me/theorems/4936452a-6dd5-4847-b696-50cf96c097c5
-- title:
--   Spherical: satake coeff
-- statement:
--   The Spherical construction uses the satake coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L328-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L328-L337

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

theorem GroundTheory.Automorphic.Spherical.satake_coeff (h : SphericalHecke μ (F := F) (n := n)) (l : Fin n → ℤ) :
    (satake μ h).coeff l = (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) *
      ∑ x ∈ cosetSupport h,
        if iwasawaExponent F n x.out = l then (h : HeckeAlgebra μ) x.out else 0 := by sorry
