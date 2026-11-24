-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PerfRetract_finite_homology_of_surjective
-- name    : GlobalTheory.CompanionTheory.PerfRetract.finite_homology_of_surjective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:26:51.808718+00:00
-- url     : https://prove2.me/theorems/4d421504-7586-4316-bd0a-f0ed3b4075df
-- title:
--   Perf Retract: finite homology of surjective
-- statement:
--   The Perf Retract construction uses the finite homology of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HomotopyProjectorComplexBounded.lean#L71-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HomotopyProjectorComplexBounded.lean#L71-L89

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HomotopyProjectorComplexBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfRetract
variable {R : Type} [CommRing R] {E : ℕ → Type} [∀ n, AddCommGroup (E n)] [∀ n, Module R (E n)]

theorem GlobalTheory.CompanionTheory.PerfRetract.finite_homology_of_surjective (C : CochainComplex (ModuleCat.{0} R) ℕ) (i j k : ℕ)
    (hi : (ComplexShape.up ℕ).prev j = i) (hk : (ComplexShape.up ℕ).next j = k)
    (W : Type) [AddCommGroup W] [Module R W] [Module.Finite R W]
    (f : W →ₗ[R] (LinearMap.ker (C.d j k).hom ⧸
      (LinearMap.range (C.d i j).hom).comap (LinearMap.ker (C.d j k).hom).subtype))
    (hf : Function.Surjective f) : Module.Finite R (C.homology j) := by sorry
