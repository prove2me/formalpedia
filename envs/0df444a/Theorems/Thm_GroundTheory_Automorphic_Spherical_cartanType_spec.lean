-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_cartanType_spec
-- name    : GroundTheory.Automorphic.Spherical.cartanType_spec
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:37:38.026802+00:00
-- url     : https://prove2.me/theorems/99261a81-d277-4988-88b2-b9eaac75f3b3
-- title:
--   Spherical: cartan Type spec
-- statement:
--   The Spherical construction uses the cartan Type spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L194-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L194-L198

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

theorem GroundTheory.Automorphic.Spherical.cartanType_spec (g : GL (Fin n) F) :
    Cartan.IsDominant (cartanType F n g) ∧
      g ∈ DoubleCoset.doubleCoset (Cartan.diagPow F n (cartanType F n g))
        (integralGL F n : Set (GL (Fin n) F)) (integralGL F n) := by sorry
