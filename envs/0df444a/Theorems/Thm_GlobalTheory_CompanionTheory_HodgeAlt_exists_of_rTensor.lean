-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_exists_of_rTensor
-- name    : GlobalTheory.CompanionTheory.HodgeAlt.exists_of_rTensor
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:25:35.863618+00:00
-- url     : https://prove2.me/theorems/a4c7a881-1852-42d4-88ea-6f26ff79934c
-- title:
--   Hodge Alt: exists of r Tensor
-- statement:
--   The Hodge Alt construction uses the exists of r Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L284-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L284-L304

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

theorem GlobalTheory.CompanionTheory.HodgeAlt.exists_of_rTensor (muF : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F)
    (hF : ∀ f ω T T' φ, muF (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T') (t : Z1 F ⊗[R] Glob1 F)
    (ht : (H1.mk F).rTensor (Glob1 F) t = 0) :
    ∃ β : A0 F, ∀ (T T' : C) (φ : T ⟶ T'), muF t T T' φ = β T' - p1 F φ (β T) := by sorry
