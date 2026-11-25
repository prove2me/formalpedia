-- Prove2me | Theorems.Thm_GlobalTheory_HolHomOnto_exists_coords
-- name    : GlobalTheory.HolHomOnto.exists_coords
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:02:41.966836+00:00
-- url     : https://prove2.me/theorems/a1577a2d-881c-581e-b077-b512eda4e962
-- title:
--   Hol Hom Onto: exists coords
-- statement:
--   The Hol Hom Onto construction uses the exists coords property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsDerivAtOfSurjective.lean#L16-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsDerivAtOfSurjective.lean#L16-L92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HolDifferentiableAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsDerivAtOfSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.HolHomOnto
open GlobalTheory.TangentOrigin GlobalTheory.HolHom

theorem GlobalTheory.HolHomOnto.exists_coords {Y : Scheme.{0}} (s : Y ⟶ Sp ℂ) [Smooth s] (x : Sp ℂ ⟶ Y) (hx : x ≫ s = 𝟙 _) :
    ∃ (n : ℕ) (U : Y.Opens) (t : Fin n → Γ(Y, U)) (W : Set (Fin n → ℂ)),
      ⊤ ≤ x ⁻¹ᵁ U ∧ IsOpen W ∧ 0 ∈ W ∧
      (∀ w ∈ W, ∃ p : Sp ℂ ⟶ Y, p ≫ s = 𝟙 _ ∧ ⊤ ≤ p ⁻¹ᵁ U ∧ ∀ i, valAt' p U (t i) = w i) ∧
      ∀ v v' : Sp (DualNumber ℂ) ⟶ Y, v ≫ s = spMap (algebraMap ℂ (DualNumber ℂ)) →
        v' ≫ s = spMap (algebraMap ℂ (DualNumber ℂ)) → spMap fstC ≫ v = x → spMap fstC ≫ v' = x →
        (∀ i, (valR v U (t i)).snd = (valR v' U (t i)).snd) → v = v' := by sorry
