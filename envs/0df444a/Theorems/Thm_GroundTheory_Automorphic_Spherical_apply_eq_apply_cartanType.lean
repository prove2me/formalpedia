-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_apply_eq_apply_cartanType
-- name    : GroundTheory.Automorphic.Spherical.apply_eq_apply_cartanType
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:30:04.72987+00:00
-- url     : https://prove2.me/theorems/c27fd714-48c1-4c81-9052-76ffb87f5b5d
-- title:
--   Spherical: apply eq apply cartan Type
-- statement:
--   The Spherical construction uses the apply eq apply cartan Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L310-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L310-L314

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

theorem GroundTheory.Automorphic.Spherical.apply_eq_apply_cartanType (h : SphericalHecke μ (F := F) (n := n)) (g : GL (Fin n) F) :
    (h : HeckeAlgebra μ) g = (h : HeckeAlgebra μ) (Cartan.diagPow F n (cartanType F n g)) := by sorry
