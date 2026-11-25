-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_ProjCoord_mem_range_chartEval
-- name    : GlobalTheory.CompanionTheory.Ar.ProjCoord.mem_range_chartEval
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:00:24.877102+00:00
-- url     : https://prove2.me/theorems/de00429d-127d-445b-8fe8-9331ec991c8e
-- title:
--   Proj Coord: mem range chart Eval
-- statement:
--   The Proj Coord construction uses the mem range chart Eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ZarhinBundleKernelFirstCoordEquations.lean#L175-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ZarhinBundleKernelFirstCoordEquations.lean#L175-L194

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

theorem GlobalTheory.CompanionTheory.Ar.ProjCoord.mem_range_chartEval (x : κ → Ω) (c : κ) (hc : x c ≠ 0) (a : Ω) :
    a ∈ (chartEval (o := o) x c hc).range ↔ a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := by sorry
