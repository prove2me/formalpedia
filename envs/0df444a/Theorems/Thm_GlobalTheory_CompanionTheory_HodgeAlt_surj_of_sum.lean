-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_surj_of_sum
-- name    : GlobalTheory.CompanionTheory.HodgeAlt.surj_of_sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:25:20.865602+00:00
-- url     : https://prove2.me/theorems/f5a3a420-e6f8-4abb-aaa3-7af3a4674622
-- title:
--   Hodge Alt: surj of sum
-- statement:
--   The Hodge Alt construction uses the surj of sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L359-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L359-L366

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_toO

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
variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]
  {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}

theorem GlobalTheory.CompanionTheory.HodgeAlt.surj_of_sum (p q : CoefMap (RingHom.id R) F G)
    (hb : Function.Surjective fun x : H1 F × H1 F ↦ p.pull1 x.1 + q.pull1 x.2)
    (hs : Function.Surjective (toO F)) : Function.Surjective (toO G) := by sorry
