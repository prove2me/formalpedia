-- Prove2me | Theorems.Thm_GlobalTheory_SplitFinitePart_exists_free_chart
-- name    : GlobalTheory.SplitFinitePart.exists_free_chart
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:25:48.232801+00:00
-- url     : https://prove2.me/theorems/eb4369a3-570a-5b29-919b-e841188913e0
-- title:
--   Split Finite Part: exists free chart
-- statement:
--   The Split Finite Part construction uses the exists free chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSectionOfIsIntegralHom.lean#L183-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSectionOfIsIntegralHom.lean#L183-L251

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSectionOfIsIntegralHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SplitFinitePart

theorem GlobalTheory.SplitFinitePart.exists_free_chart {R : Type} [CommRing R] {Z : Scheme.{0}} (π : Z ⟶ Sp R) [Flat π]
    [LocallyOfFinitePresentation π] (p : PrimeSpectrum R) (W W' : (Sp R).Opens) (H : Z.Opens)
    (ρ : H.toScheme ⟶ W.toScheme) (hW : p ∈ W) (hW' : p ∈ W') (hρ : ρ ≫ W.ι = H.ι ≫ π) [IsFinite ρ] :
    ∃ (f : R) (B : Type) (_ : CommRing B) (_ : Algebra (Localization.Away f) B) (j : Sp B ⟶ Z), f ∉ p.asIdeal ∧
      Module.Finite (Localization.Away f) B ∧ Module.Free (Localization.Away f) B ∧ IsOpenImmersion j ∧
      j ≫ π = spMap (algebraMap (Localization.Away f) B) ≫ spMap (algebraMap R (Localization.Away f)) ∧
      Set.range (spMap (algebraMap R (Localization.Away f))) ⊆ (W : Set (Sp R)) ∩ W' ∧
      Set.range j = (H : Set Z) ∩ π ⁻¹' Set.range (spMap (algebraMap R (Localization.Away f))) := by sorry
