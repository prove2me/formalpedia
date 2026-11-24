-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_exists_prim_cochain
-- name    : GlobalTheory.CompanionTheory.Hodge.LiftO.exists_prim_cochain
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:21:02.556659+00:00
-- url     : https://prove2.me/theorems/232f1ffd-093c-4d07-9798-626ed1adaf04
-- title:
--   Lift O: exists prim cochain
-- statement:
--   The Lift O construction uses the exists prim cochain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean#L195-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean#L195-L202

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

theorem GlobalTheory.CompanionTheory.Hodge.LiftO.exists_prim_cochain (m p q : CoefMap (RingHom.id R) F G)
    (hm1 : ∀ c, m.pull1 c = p.pull1 c + q.pull1 c) (f : Z1 F) :
    ∃ g : C0 G, ∀ ⦃T T' : E⦄ (φ : T ⟶ T'), g T' - mp G φ (g T) =
      (m.pullbackOneCocycle f).1 T T' φ - ((p.pullbackOneCocycle f).1 T T' φ + (q.pullbackOneCocycle f).1 T T' φ) := by sorry
