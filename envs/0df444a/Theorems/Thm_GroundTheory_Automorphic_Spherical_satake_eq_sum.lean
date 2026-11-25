-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_satake_eq_sum
-- name    : GroundTheory.Automorphic.Spherical.satake_eq_sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:16:32.284008+00:00
-- url     : https://prove2.me/theorems/91edb175-2216-5d66-b26f-47d91511b0b1
-- title:
--   Spherical: satake eq sum
-- statement:
--   The Spherical construction uses the satake eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalSatake.lean#L196-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalSatake.lean#L196-L206

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalPrincipal
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalSatake
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
open MeasureTheory Matrix GLnLocal Iwasawa Parabolic HeckeAlgebra AddMonoidAlgebra
open scoped ValuativeRel
open GroundTheory.Automorphic.Spherical
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem GroundTheory.Automorphic.Spherical.satake_eq_sum (h : SphericalHecke μ (F := F) (n := n))
    (S : Finset (GL (Fin n) F ⧸ integralGL F n)) (hS : ∀ x ∉ S, (h : HeckeAlgebra μ) x.out = 0) :
    satake μ h = (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) •
      ∑ x ∈ S, single (iwasawaExponent F n x.out) ((h : HeckeAlgebra μ) x.out) := by sorry
