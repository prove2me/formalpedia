-- Prove2me | Theorems.Thm_GlobalTheory_ChartCubExt_isPullCubical_of_generic_of_ext
-- name    : GlobalTheory.ChartCubExt.isPullCubical_of_generic_of_ext
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:52:41.5618+00:00
-- url     : https://prove2.me/theorems/00454ec2-e17e-4c6e-a669-5d63c2b591d7
-- title:
--   Chart Cub Ext: is Pull Cubical of generic of ext
-- statement:
--   The Chart Cub Ext construction uses the is Pull Cubical of generic of ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsPullCubicalOfGenericOfExt.lean#L25-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsPullCubicalOfGenericOfExt.lean#L25-L115

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SabMapOfIsoOfExtendGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsPullCubicalOfGenericOfExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ChartCubExt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Exist.CubicalExtension
variable {T K : Type} [CommRing T] [IsDomain T] [Field K] [Algebra T K] [IsFractionRing T K]

theorem GlobalTheory.ChartCubExt.isPullCubical_of_generic_of_ext (hE : ExtendGenAt T K) {S : Scheme.{0}} {G₀ : Over S} {G : Over (Sp T)}
    {GK : Over (Sp K)} [GrpObj G₀] [IsCommMonObj G₀] [GrpObj G] [IsCommMonObj G] [GrpObj GK] [IsCommMonObj GK]
    (hG : IsSemiAbelian G) {L₀ : RigLB G₀} {L : RigLB G} {LK : RigLB GK} (c₀ : CubicalStr G₀ L₀)
    (c : CubicalStr G L) (cK : CubicalStr GK LK) (n : CubeMap G G₀) (m : CubeMap GK G) (m' : CubeMap GK G₀)
    (hp : IsPullback m.F GK.hom G.hom (spMap (algebraMap T K))) (he : m.e = spMap (algebraMap T K))
    (h₁ : m'.F = m.F ≫ n.F) (h₂ : m'.F3 = m.F3 ≫ n.F3) (h₃ : m'.e = m.e ≫ n.e)
    (H' : m.IsPullCubical cK c) (H'' : m'.IsPullCubical cK c₀) : n.IsPullCubical c c₀ := by sorry
