-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuasiRefl_exists_unitary_carry
-- name    : GlobalTheory.CompanionTheory.SW.QuasiRefl.exists_unitary_carry
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:20.978361+00:00
-- url     : https://prove2.me/theorems/c12cabeb-c701-43c4-b5c5-222cf855599f
-- title:
--   Quasi Refl: exists unitary carry
-- statement:
--   The Quasi Refl construction uses the exists unitary carry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GermConstantsEqAlongAffineSpaceSquare.lean#L100-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GermConstantsEqAlongAffineSpaceSquare.lean#L100-L154

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GermConstantsEqAlongAffineSpaceSquare
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuasiRefl
open HeckeCharacterZeroLocus.SiegelWeilU

theorem GlobalTheory.CompanionTheory.SW.QuasiRefl.exists_unitary_carry (A : Type) [CommRing A] (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) A) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → A) (ε : A)
    (hxy : hform σ J x x = hform σ J y y) (hβ : IsUnit (hform σ J x x)) (hε : ε * σ ε = 1)
    (hu : IsUnit (hform σ J x x - σ ε * hform σ J y x)) :
    ∃ g ∈ UJ σ J, (g : Matrix (Fin M) (Fin M) A) *ᵥ x = y ∧
      ∀ z, hform σ J x z = 0 → hform σ J y z = 0 → (g : Matrix (Fin M) (Fin M) A) *ᵥ z = z := by sorry
