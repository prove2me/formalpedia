-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_exists_prim
-- name    : GlobalTheory.CompanionTheory.Hodge.LiftO.exists_prim
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:22:47.061854+00:00
-- url     : https://prove2.me/theorems/52171f63-9493-43ad-8a61-da1e48f5de0b
-- title:
--   Lift O: exists prim
-- statement:
--   The Lift O construction uses the exists prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean#L243-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean#L243-L264

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

theorem GlobalTheory.CompanionTheory.Hodge.LiftO.exists_prim (muF : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F)
    (hF : ∀ f ω T T' φ, muF (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (t : Z1 F ⊗[R] Glob1 F) (h0 : (H1.mk F).rTensor (Glob1 F) t = 0) :
    ∃ β : A0 F, ∀ T T' φ, muF t T T' φ = β T' - p1 F φ (β T) := by sorry
