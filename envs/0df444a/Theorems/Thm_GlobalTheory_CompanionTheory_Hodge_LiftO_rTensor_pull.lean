-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_rTensor_pull
-- name    : GlobalTheory.CompanionTheory.Hodge.LiftO.rTensor_pull
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:22:49.767249+00:00
-- url     : https://prove2.me/theorems/ad508d33-918e-450f-95b7-dfcd73171cea
-- title:
--   Lift O: r Tensor pull
-- statement:
--   The Lift O construction uses the r Tensor pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean#L187-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean#L187-L193

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorPairingIotaTwo
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge GlobalTheory.CompanionTheory.Hodge.LiftO
variable {R : Type} [CommRing R] {C E : Type} [Category.{0} C] [Category.{0} E]
  {F : C ⥤ CommAlgCat.{0} R} {G : E ⥤ CommAlgCat.{0} R}

theorem GlobalTheory.CompanionTheory.Hodge.LiftO.rTensor_pull (m : CoefMap (RingHom.id R) F G) (t : Z1 F ⊗[R] Glob1 F) :
    (H1.mk G).rTensor (Glob1 G) (TensorProduct.map m.pullbackOneCocycle (pullGlob1 m) t) =
      TensorProduct.map m.pull1 (pullGlob1 m) ((H1.mk F).rTensor (Glob1 F) t) := by sorry
