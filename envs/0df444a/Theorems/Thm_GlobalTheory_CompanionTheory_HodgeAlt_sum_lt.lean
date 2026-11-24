-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_sum_lt
-- name    : GlobalTheory.CompanionTheory.HodgeAlt.sum_lt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:25:07.385198+00:00
-- url     : https://prove2.me/theorems/8e8fc251-9c8b-46f7-869a-b734ec656101
-- title:
--   Hodge Alt: sum lt
-- statement:
--   The Hodge Alt construction uses the sum lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L157-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L157-L184

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

theorem GlobalTheory.CompanionTheory.HodgeAlt.sum_lt {M : Type} [AddCommGroup M] [Module R M] {n : ℕ} (u v : Fin n → R)
    (c : Fin n → Fin n → M) (hd : ∀ i, c i i = 0) (ha : ∀ i j, c j i = -c i j) :
    ∑ i, ∑ j, (u i * v j) • c i j =
      ∑ i, ∑ j, if i < j then (u i * v j - u j * v i) • c i j else 0 := by sorry
