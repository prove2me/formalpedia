-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_eq_zero_of_alt
-- name    : GlobalTheory.CompanionTheory.HodgeAlt.eq_zero_of_alt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:25:15.241798+00:00
-- url     : https://prove2.me/theorems/bcbeeac9-9be3-473f-a1dc-f0de07f8d2c8
-- title:
--   Hodge Alt: eq zero of alt
-- statement:
--   The Hodge Alt construction uses the eq zero of alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L203-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L203-L232

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
variable {R V V' : Type} [CommRing R] [AddCommGroup V] [AddCommGroup V'] [Module R V] [Module R V']

theorem GlobalTheory.CompanionTheory.HodgeAlt.eq_zero_of_alt [Module.Finite R V] [Module.Projective R V] (τ : ⋀[R]^2 V)
    (h : ∀ l l' : V →ₗ[R] R, alt l l' τ = 0) : τ = 0 := by sorry
