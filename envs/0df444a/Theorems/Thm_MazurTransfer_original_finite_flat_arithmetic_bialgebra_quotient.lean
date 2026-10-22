-- Prove2me | Theorems.Thm_MazurTransfer_original_finite_flat_arithmetic_bialgebra_quotient
-- name    : MazurTransfer.original_finite_flat_arithmetic_bialgebra_quotient
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T06:51:33.912982+00:00
-- url     : https://prove2.me/theorems/e00cfd7b-68f4-41c7-9c78-ca2de9f5b240
-- statement:
--   Over the same original PID base and fraction field, the original equivariant surjective quotient of the additive arithmetic point labels is represented by a finite-flat cocommutative Hopf quotient with a genuine injective bialgebra inclusion into the original Hopf algebra. Its original addition, Galois action and exact point-restriction compatibility are retained. All original ring, field, scalar tower, finite-flat, fixed-field and algebraic-closure hypotheses are retained. Named downstream consumer: actual selected arithmetic norm-kernel character quotients and their original integral norm torsor pushforwards.

import Definitions.Def_FiniteFlat_ClosureHopf
noncomputable section
open scoped TensorProduct
open WithConv

theorem MazurTransfer.original_finite_flat_arithmetic_bialgebra_quotient : ∀ {R : Type} [CommRing R] {G : Type} [CommRing G] [HopfAlgebra R G]
  {F : Type} [Field F] [Algebra R F] {L : Type} [Field L] [Algebra R L] [Algebra F L]
  [IsScalarTower R F L]
  {M : Type} [AddCommGroup M] [DistribMulAction (L ≃ₐ[F] L) M]
  (e : WithConv (G →ₐ[R] L) ≃ M)
  (he_add : ∀ f g, e (f * g) = e f + e g)
  (he_act : ∀ (σ : L ≃ₐ[F] L) (f g : WithConv (G →ₐ[R] L)),
    (∀ x : G, g x = σ (f x)) → e g = σ • (e f))
  {N : Type} [AddCommGroup N] [DistribMulAction (L ≃ₐ[F] L) N]
  (π : M →+ N) (hπ : Function.Surjective π)
  (hπ_act : ∀ (σ : L ≃ₐ[F] L) (m : M), π (σ • m) = σ • (π m))
  [IsDomain R] [IsPrincipalIdealRing R] [Module.Finite R G] [Module.Flat R G]
  [Coalgebra.IsCocomm R G] [IsFractionRing R F] [CharZero F]
  (hfix : ∀ c : L, (∀ σ : L ≃ₐ[F] L, σ c = c) → c ∈ Set.range (algebraMap F L))
  [IsAlgClosed L] [CharZero L],
∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ (ι : H →ₐc[R] G) (e' : WithConv (H →ₐ[R] L) ≃ N),
        Function.Injective ι ∧
        (∀ f g, e' (f * g) = e' f + e' g) ∧
        (∀ (σ : L ≃ₐ[F] L) (f g : WithConv (H →ₐ[R] L)),
          (∀ x : H, g x = σ (f x)) → e' g = σ • (e' f)) ∧
        (∀ φ : WithConv (G →ₐ[R] L),
          e' (WithConv.toConv ((WithConv.ofConv φ).comp (ι : H →ₐ[R] G))) = π (e φ)) := by sorry
