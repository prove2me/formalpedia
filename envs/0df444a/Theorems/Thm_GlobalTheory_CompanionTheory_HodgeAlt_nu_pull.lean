-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_nu_pull
-- name    : GlobalTheory.CompanionTheory.HodgeAlt.nu_pull
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:25:39.8048+00:00
-- url     : https://prove2.me/theorems/63dc4225-3a7a-41a1-9546-31441e6a992e
-- title:
--   Hodge Alt: nu pull
-- statement:
--   The Hodge Alt construction uses the nu pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L405-L417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L405-L417

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeAlt
variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]
  {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}

theorem GlobalTheory.CompanionTheory.HodgeAlt.nu_pull (m : CoefMap (RingHom.id R) F G) (nuF : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2)
    (nuG : ⋀[R]^2 (Glob1 G) →ₗ[R] W0 G 2)
    (hF : ∀ a b T, nuF (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hG : ∀ a b T, nuG (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (τ : ⋀[R]^2 (Glob1 F)) (T : D) :
    nuG (exteriorPower.map 2 (pullGlob1 m) τ) T = qOm m 2 T (nuF τ (m.G.obj T)) := by sorry
