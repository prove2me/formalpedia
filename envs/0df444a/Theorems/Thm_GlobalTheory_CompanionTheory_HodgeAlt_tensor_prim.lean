-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_tensor_prim
-- name    : GlobalTheory.CompanionTheory.HodgeAlt.tensor_prim
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:25:23.205802+00:00
-- url     : https://prove2.me/theorems/8849d03b-31c4-46eb-98ca-4f72b1531211
-- title:
--   Hodge Alt: tensor prim
-- statement:
--   The Hodge Alt construction uses the tensor prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L104-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L104-L125

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
variable {R V V' W W' : Type} [CommRing R] [AddCommGroup V] [AddCommGroup V'] [AddCommGroup W]
  [AddCommGroup W'] [Module R V] [Module R V'] [Module R W] [Module R W']

theorem GlobalTheory.CompanionTheory.HodgeAlt.tensor_prim (p q m : V →ₗ[R] V') (p' q' m' : W →ₗ[R] W') (P : V' →ₗ[R] V) (Q : W' →ₗ[R] W)
    (hPp : ∀ v, P (p v) = v) (hPq : ∀ v, P (q v) = 0) (hQp : ∀ w, Q (p' w) = 0)
    (hQq : ∀ w, Q (q' w) = w) (hm : ∀ v, m v = p v + q v) (hm' : ∀ w, m' w = p' w + q' w)
    (t : V ⊗[R] W)
    (ht : TensorProduct.map m m' t = TensorProduct.map p p' t + TensorProduct.map q q' t) : t = 0 := by sorry
