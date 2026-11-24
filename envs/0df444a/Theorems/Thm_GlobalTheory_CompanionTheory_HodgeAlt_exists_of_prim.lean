-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_exists_of_prim
-- name    : GlobalTheory.CompanionTheory.HodgeAlt.exists_of_prim
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:28:34.141619+00:00
-- url     : https://prove2.me/theorems/916b0e5c-c62b-4058-b268-5757f0a1062e
-- title:
--   Hodge Alt: exists of prim
-- statement:
--   The Hodge Alt construction uses the exists of prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L328-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L328-L341

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
variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]
  {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}

theorem GlobalTheory.CompanionTheory.HodgeAlt.exists_of_prim (m p q : CoefMap (RingHom.id R) F G) (z : cechDeRhamTotalCocyclesTwo F) (hz : z.1.1 = 0)
    (h : pullHyp2 m (Hyp2.mk F z) = pullHyp2 p (Hyp2.mk F z) + pullHyp2 q (Hyp2.mk F z)) :
    ∃ e : Tot1 G, dTot1 G e = ((0 : C2 G),
      (pullTot2 m z.1 - pullTot2 p z.1 - pullTot2 q z.1).2.1,
      (pullTot2 m z.1 - pullTot2 p z.1 - pullTot2 q z.1).2.2) := by sorry
