-- Prove2me | Theorems.Thm_GlobalTheory_SplitFinitePart_exists_free_away
-- name    : GlobalTheory.SplitFinitePart.exists_free_away
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:19:47.121899+00:00
-- url     : https://prove2.me/theorems/eaf71d01-6d4b-42e0-a459-580d7c279f4f
-- title:
--   Split Finite Part: exists free away
-- statement:
--   The Split Finite Part construction uses the exists free away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSectionOfIsIntegralHom.lean#L148-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSectionOfIsIntegralHom.lean#L148-L181

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

theorem GlobalTheory.SplitFinitePart.exists_free_away {R : Type} [CommRing R] (f₀ : R) (p : PrimeSpectrum R) (hp : f₀ ∉ p.asIdeal) (B : Type)
    [CommRing B] [Algebra (Localization.Away f₀) B] [Module.Finite (Localization.Away f₀) B]
    [Module.Flat (Localization.Away f₀) B] [Algebra.FinitePresentation (Localization.Away f₀) B] :
    ∃ (f : R) (_ : Algebra (Localization.Away f₀) (Localization.Away f)), f ∉ p.asIdeal ∧
      IsScalarTower R (Localization.Away f₀) (Localization.Away f) ∧
      Module.Free (Localization.Away f) (Localization.Away f ⊗[Localization.Away f₀] B) := by sorry
