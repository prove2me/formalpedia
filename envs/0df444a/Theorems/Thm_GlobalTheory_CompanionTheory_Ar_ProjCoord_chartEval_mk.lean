-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_ProjCoord_chartEval_mk
-- name    : GlobalTheory.CompanionTheory.Ar.ProjCoord.chartEval_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:01.736121+00:00
-- url     : https://prove2.me/theorems/cd555633-8334-4dfc-a8b5-8715e5d4398b
-- title:
--   Proj Coord: chart Eval mk
-- statement:
--   The Proj Coord construction uses the chart Eval mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ZarhinBundleKernelFirstCoordEquations.lean#L168-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ZarhinBundleKernelFirstCoordEquations.lean#L168-L173

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

theorem GlobalTheory.CompanionTheory.Ar.ProjCoord.chartEval_mk (x : κ → Ω) (c : κ) (hc : x c ≠ 0) (n : ℕ) (a : MvPolynomial κ o)
    (ha : a ∈ homogeneousSubmodule κ o (n • 1)) :
    chartEval x c hc (Away.mk _ (X_mem c) n a ha) = aeval x a / x c ^ n := by sorry
