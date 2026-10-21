-- Prove2me | Theorems.Thm_MazurTransfer_original_positive_scalar_norm_factors_finite_flat
-- name    : MazurTransfer.original_positive_scalar_norm_factors_finite_flat
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T04:50:00.381944+00:00
-- url     : https://prove2.me/theorems/52b3350a-b14d-48a2-9b25-cbe4d132e930
-- statement:
--   The same two relative endomorphisms whose two composites equal the same positive scalar on the original abelian scheme are finite, flat, locally finitely presented and surjective. The exact original Noetherian base, abelian scheme, scalar, positivity and both composition equalities are retained. Named downstream consumer: actual integral nineteen norm models, including at nineteen.

import Theorems.Thm_MazurTransfer_original_abelian_scheme_finite_endomorphism_flat
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul
noncomputable section
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem MazurTransfer.original_positive_scalar_norm_factors_finite_flat : ∀ {R : Type} [CommRing R] [IsNoetherianRing R] {A : Scheme}
    {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hcomm : L.IsCommutative) (hA : AbelianSchemePropertyBundle R f)
    (n : ℕ) (hn : 0 < n) (φ ψ : SchemeHomOver f f)
    (hφψ : φ.val ≫ ψ.val = L.schemeNsmul n)
    (hψφ : ψ.val ≫ φ.val = L.schemeNsmul n),
(IsFinite φ.val ∧ Flat φ.val ∧ LocallyOfFinitePresentation φ.val ∧ Surjective φ.val) ∧
    (IsFinite ψ.val ∧ Flat ψ.val ∧ LocallyOfFinitePresentation ψ.val ∧ Surjective ψ.val) := by sorry
