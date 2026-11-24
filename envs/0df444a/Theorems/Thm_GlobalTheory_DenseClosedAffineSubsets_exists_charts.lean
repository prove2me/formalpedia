-- Prove2me | Theorems.Thm_GlobalTheory_DenseClosedAffineSubsets_exists_charts
-- name    : GlobalTheory.DenseClosedAffineSubsets.exists_charts
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:44:06.008386+00:00
-- url     : https://prove2.me/theorems/df30ce6e-6ef3-467a-8341-f8f513ae1f52
-- title:
--   Dense Closed Affine Subsets: exists charts
-- statement:
--   The Dense Closed Affine Subsets construction uses the exists charts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineLeOrDisjoint.lean#L213-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineLeOrDisjoint.lean#L213-L268

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineLeOrDisjoint
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.DenseClosedAffineSubsets
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GlobalTheory.DenseClosedAffineSubsets.exists_charts (R : Type) [CommRing R] (N : ℕ) :
    ∃ (D : Fin (N + 1) → (PSpace R N).Opens) (r : ∀ _ K, Γ((D K).toScheme, ⊤)),
      ⨆ K, D K = ⊤ ∧ (∀ J K, (D K).toScheme.basicOpen (r J K) ≤ (D K).ι ⁻¹ᵁ D J) ∧
      ∀ (U : Scheme.{0}) (u : U ⟶ Sp R) (m : Fin (N + 1) → Γ(U, ⊤)) (K₀ : Fin (N + 1)),
        IsUnit (m K₀) → ∃ φ : U ⟶ PSpace R N, φ ≫ PSpace.str R N = u ∧
          ∀ (K : Fin (N + 1)) (V : Scheme.{0}) (a : V ⟶ U) (b : V ⟶ D K), a ≫ φ = b ≫ (D K).ι →
            IsUnit (a.appTop (m K)) ∧
              ∀ J, b.appTop (r J K) * a.appTop (m K) = a.appTop (m J) := by sorry
