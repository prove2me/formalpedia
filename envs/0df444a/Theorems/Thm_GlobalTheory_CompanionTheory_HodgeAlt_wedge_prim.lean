-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_wedge_prim
-- name    : GlobalTheory.CompanionTheory.HodgeAlt.wedge_prim
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:25:34.557317+00:00
-- url     : https://prove2.me/theorems/6c2232be-e0e3-4f47-80e1-51b6f7782274
-- title:
--   Hodge Alt: wedge prim
-- statement:
--   The Hodge Alt construction uses the wedge prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L234-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L234-L253

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

theorem GlobalTheory.CompanionTheory.HodgeAlt.wedge_prim [Module.Finite R V] [Module.Projective R V] (p q m : V →ₗ[R] V')
    (P Q : V' →ₗ[R] V) (hPp : ∀ v, P (p v) = v) (hPq : ∀ v, P (q v) = 0) (hQp : ∀ v, Q (p v) = 0)
    (hQq : ∀ v, Q (q v) = v) (hm : ∀ v, m v = p v + q v) (τ : ⋀[R]^2 V)
    (h : exteriorPower.map 2 m τ = exteriorPower.map 2 p τ + exteriorPower.map 2 q τ) : τ = 0 := by sorry
