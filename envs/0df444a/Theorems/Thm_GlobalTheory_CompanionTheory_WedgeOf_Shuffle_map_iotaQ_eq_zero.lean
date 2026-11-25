-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_Shuffle_map_iotaQ_eq_zero
-- name    : GlobalTheory.CompanionTheory.WedgeOf.Shuffle.map_iotaQ_eq_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:58:27.843193+00:00
-- url     : https://prove2.me/theorems/48956e5d-df79-54d0-af2a-2c2bba93eceb
-- title:
--   Shuffle: map iota Q eq zero
-- statement:
--   The Shuffle construction uses the map iota Q eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CrossProductKernelQuotientVanishing.lean#L189-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CrossProductKernelQuotientVanishing.lean#L189-L214

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CrossProductKernelQuotientVanishing
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf GlobalTheory.CompanionTheory.WedgeOf.Shuffle
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F}
variable (F)

theorem GlobalTheory.CompanionTheory.WedgeOf.Shuffle.map_iotaQ_eq_zero (R : Type) [CommRing R] (C : Type) [Category.{0} C] [Finite C] [Quiver.IsThin C]
    (F : C ⥤ CommAlgCat.{0} R) (t : H1 F ⊗[R] H1 F) (ht : TensorProduct.lift (crossB F) t = 0) :
    TensorProduct.map (iotaQ F) (iotaQ F) t = 0 := by sorry
