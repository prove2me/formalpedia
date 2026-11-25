-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_ProjCoord_chartEval_injective
-- name    : GlobalTheory.CompanionTheory.Ar.ProjCoord.chartEval_injective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:59:54.049548+00:00
-- url     : https://prove2.me/theorems/5ed143f9-9e7c-5149-8514-6c97fc202c1a
-- title:
--   Proj Coord: chart Eval injective
-- statement:
--   The Proj Coord construction uses the chart Eval injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ZarhinBundleKernelFirstCoordEquations.lean#L196-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ZarhinBundleKernelFirstCoordEquations.lean#L196-L205

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_ZarhinBundleKernelFirstCoordEquations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.ProjCoord
open MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
variable {o κ Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem GlobalTheory.CompanionTheory.Ar.ProjCoord.chartEval_injective (x : κ → Ω) (c : κ) (hc : x c ≠ 0)
    (hinj : ∀ (n : ℕ) (g : MvPolynomial κ o), g.IsHomogeneous n → aeval x g = 0 → g = 0) :
    Function.Injective (chartEval (o := o) x c hc) := by sorry
