-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_mu_pull
-- name    : GlobalTheory.CompanionTheory.Hodge.LiftO.mu_pull
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:25:01.252574+00:00
-- url     : https://prove2.me/theorems/71063f33-cdd9-4a93-80d7-a361125e716a
-- title:
--   Lift O: mu pull
-- statement:
--   The Lift O construction uses the mu pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean#L175-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean#L175-L185

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

theorem GlobalTheory.CompanionTheory.Hodge.LiftO.mu_pull (m : CoefMap (RingHom.id R) F G)
    (muF : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F) (muG : Z1 G ⊗[R] Glob1 G →ₗ[R] A1 G)
    (hF : ∀ f ω T T' φ, muF (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (hG : ∀ f ω T T' φ, muG (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (t : Z1 F ⊗[R] Glob1 F) {T T' : E} (φ : T ⟶ T') :
    muG (TensorProduct.map m.pullbackOneCocycle (pullGlob1 m) t) T T' φ = q1 m T' (muF t _ _ (m.G.map φ)) := by sorry
