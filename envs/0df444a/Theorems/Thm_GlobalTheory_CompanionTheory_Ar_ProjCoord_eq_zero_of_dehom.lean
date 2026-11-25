-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_ProjCoord_eq_zero_of_dehom
-- name    : GlobalTheory.CompanionTheory.Ar.ProjCoord.eq_zero_of_dehom
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:00:10.30989+00:00
-- url     : https://prove2.me/theorems/fe495d4f-46b3-59dc-b1b6-22fd8f8b9364
-- title:
--   Proj Coord: eq zero of dehom
-- statement:
--   The Proj Coord construction uses the eq zero of dehom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ZarhinBundleKernelFirstCoordEquations.lean#L219-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ZarhinBundleKernelFirstCoordEquations.lean#L219-L237

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

theorem GlobalTheory.CompanionTheory.Ar.ProjCoord.eq_zero_of_dehom [IsDomain o] {ι : Type} {n : ℕ} {g : MvPolynomial (Option ι) o}
    (hg : g.IsHomogeneous n)
    (h : aeval (fun j : Option ι => (j.elim 1 X : MvPolynomial ι o)) g = 0) : g = 0 := by sorry
