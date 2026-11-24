-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_inv_mem
-- name    : GlobalTheory.CompanionTheory.Ar.CoordModel.inv_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:03:42.93558+00:00
-- url     : https://prove2.me/theorems/8a3cc896-2ea1-43ef-977a-705e95682adc
-- title:
--   Coord Model: inv mem
-- statement:
--   The Coord Model construction uses the inv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L104-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L104-L114

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.CoordModel
open AlgebraicGeometry CategoryTheory
variable (A : Type) [CommRing A] (Ω : Type) [Field Ω] [Algebra A Ω]
variable [IsDomain A] [IsFractionRing A Ω]
omit [IsDomain A] [IsFractionRing A Ω]

theorem GlobalTheory.CompanionTheory.Ar.CoordModel.inv_mem {κ : Type} {x : κ → A} (hx : Ideal.span (Set.range x) = ⊤) (c : κ) (S : Subring Ω)
    (hA : ∀ a, algebraMap A Ω a ∈ S) (hS : ∀ j, algebraMap A Ω (x j) / algebraMap A Ω (x c) ∈ S) :
    (algebraMap A Ω (x c))⁻¹ ∈ S := by sorry
