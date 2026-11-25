-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_satakeHom_apply
-- name    : GroundTheory.Automorphic.Spherical.satakeHom_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:17:23.040839+00:00
-- url     : https://prove2.me/theorems/cf446db3-7775-4c9e-99fd-31b82229bc95
-- title:
--   Spherical: satake Hom apply
-- statement:
--   The Spherical construction uses the satake Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalSatake.lean#L226-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalSatake.lean#L226-L226

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

theorem GroundTheory.Automorphic.Spherical.satakeHom_apply (h : SphericalHecke μ (F := F) (n := n)) : satakeHom μ h = satake μ h := by sorry
