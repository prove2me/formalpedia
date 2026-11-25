-- Prove2me | Theorems.Thm_GlobalTheory_SplitFinitePart_exists_finite_open
-- name    : GlobalTheory.SplitFinitePart.exists_finite_open
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:30.270474+00:00
-- url     : https://prove2.me/theorems/1a915dc0-c245-4429-b37f-e8450dd58a1f
-- title:
--   Split Finite Part: exists finite open
-- statement:
--   The Split Finite Part construction uses the exists finite open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSectionOfIsIntegralHom.lean#L43-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSectionOfIsIntegralHom.lean#L43-L141

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

theorem GlobalTheory.SplitFinitePart.exists_finite_open {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K]
    [Algebra R K] [IsFractionRing R K] {Z : Scheme.{0}} (π : Z ⟶ Sp R) [Flat π] [LocallyQuasiFinite π]
    [IsSeparated π] [QuasiCompact π] [LocallyOfFiniteType π]
    (hs : ∀ z : Z, π z = genericPoint (Sp R) →
      ∃ γ : Sp K ⟶ Z, γ ≫ π = spMap (algebraMap R K) ∧ z ∈ Set.range γ) (p : Sp R) :
    ∃ (W : (Sp R).Opens) (H : Z.Opens) (ρ : H.toScheme ⟶ W.toScheme), p ∈ W ∧ ρ ≫ W.ι = H.ι ≫ π ∧ IsFinite ρ ∧
      (∀ z : Z, π z = p → z ∈ H) ∧
      ∀ z ∈ H, ∃ s : W.toScheme ⟶ Z, s ≫ π = W.ι ∧ (∀ w, s w ∈ H) ∧ z ∈ Set.range s := by sorry
