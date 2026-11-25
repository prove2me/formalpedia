-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_ProjCoord_exists_mem_basicOpen
-- name    : GlobalTheory.CompanionTheory.Ar.ProjCoord.exists_mem_basicOpen
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:00:15.204464+00:00
-- url     : https://prove2.me/theorems/813f680c-b504-5bac-bee0-51dd622d9c9f
-- title:
--   Proj Coord: exists mem basic Open
-- statement:
--   The Proj Coord construction uses the exists mem basic Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ZarhinBundleKernelFirstCoordEquations.lean#L207-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ZarhinBundleKernelFirstCoordEquations.lean#L207-L217

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

theorem GlobalTheory.CompanionTheory.Ar.ProjCoord.exists_mem_basicOpen (q : Proj (homogeneousSubmodule κ o)) :
    ∃ c, q ∈ Proj.basicOpen (homogeneousSubmodule κ o) (X c) := by sorry
