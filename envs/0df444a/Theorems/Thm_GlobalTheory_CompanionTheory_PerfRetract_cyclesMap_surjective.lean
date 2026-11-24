-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PerfRetract_cyclesMap_surjective
-- name    : GlobalTheory.CompanionTheory.PerfRetract.cyclesMap_surjective
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:27:01.863874+00:00
-- url     : https://prove2.me/theorems/d73c088f-b002-48b9-8edd-1dcbd10be18b
-- title:
--   Perf Retract: cycles Map surjective
-- statement:
--   The Perf Retract construction uses the cycles Map surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HomotopyProjectorComplexBounded.lean#L101-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HomotopyProjectorComplexBounded.lean#L101-L112

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

theorem GlobalTheory.CompanionTheory.PerfRetract.cyclesMap_surjective (d : ∀ n, E n →ₗ[R] E (n + 1))
    (C : CochainComplex (ModuleCat.{0} R) ℕ) (inc : ∀ n, C.X n →ₗ[R] E n)
    (r : ∀ n, E n →ₗ[R] C.X n) (hri : ∀ p, r p ∘ₗ inc p = LinearMap.id)
    (hinc : ∀ p, inc (p + 1) ∘ₗ (C.d p (p + 1)).hom = d p ∘ₗ inc p)
    (hr : ∀ p, r (p + 1) ∘ₗ d p = (C.d p (p + 1)).hom ∘ₗ r p) (j : ℕ) :
    Function.Surjective (cyclesMap d C r hr j) := by sorry
