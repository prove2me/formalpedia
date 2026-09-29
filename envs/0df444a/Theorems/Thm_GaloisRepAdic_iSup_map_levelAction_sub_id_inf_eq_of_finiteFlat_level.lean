-- Prove2me | Theorems.Thm_GaloisRepAdic_iSup_map_levelAction_sub_id_inf_eq_of_finiteFlat_level
-- name    : GaloisRepAdic.iSup_map_levelAction_sub_id_inf_eq_of_finiteFlat_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/ade06cfa-fb84-5914-b9fb-71954c1f3a41
-- title:
--   Inertia augmentation and Galois-stable submodules of a finite flat level
-- statement:
--   Let $A$ be a commutative local ring and let $\rho$ be an adic Galois representation over $A$: a free finite $A$-module $V$ of rank $2$ together with a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ (the $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`) to $\mathrm{End}_A(V)$ satisfying the adic continuity condition. Let $p$ be a prime with $p \neq 2$ whose image in $A$ lies in the maximal ideal, and let $I$ be an ideal of $A$ with $A/I$ finite; write $\rho.\mathrm{levelAction}\,I\,\sigma$ for the endomorphism of the level $V/I\cdot V$ induced by $\rho(\sigma)$. Assume the level is finite flat in the following sense: there is a commutative ring $H$, a Hopf algebra over the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb Q$ consisting of the rationals whose denominator is coprime to $p$, module-finite and flat over that subring and with cocommutative comultiplication, and a bijection $e$ from the convolution monoid `WithConv` of algebra homomorphisms $H \to \overline{\mathbb Q}$ over that subring onto $V/I\cdot V$, such that $e(fg) = e(f) + e(g)$ and, whenever $g(h) = \sigma(f(h))$ for all $h \in H$, one has $e(g) = (\rho.\mathrm{levelAction}\,I\,\sigma)(e(f))$. Let $P$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a nonunit of $P$, and write $\mathcal I_P$ for the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $P$ inside its decomposition subgroup. Finally let $N$ be an $A$-submodule of $V/I\cdot V$ with $N$ mapped into itself by $\rho.\mathrm{levelAction}\,I\,\sigma$ for every $\sigma$. Then
--   $$\Big(\sum_{\sigma \in \mathcal I_P} (\sigma - 1)(V/I\cdot V)\Big) \cap N = \sum_{\sigma \in \mathcal I_P} (\sigma - 1)N,$$
--   where $\sigma - 1$ abbreviates $\rho.\mathrm{levelAction}\,I\,\sigma - \mathrm{id}$ and the sums are suprema of submodules indexed by the elements of $\mathcal I_P$.
--
--   The assertion is that on a level admitting a finite flat model over $\mathbb Z_{(p)}$ with $p$ odd, the inertia-augmentation submodule $J(M) = \sum_{\sigma \in \mathcal I_P}(\sigma-1)M$, and hence the passage to inertia coinvariants $M \mapsto M/J(M)$, behaves left exactly on Galois-stable submodules of the level. It is used in the deduction that a representation which is flat at $p$ and whose residual representation is ordinary at $p$ is itself ordinary at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_iSup_map_levelAction_sub_id_inf_eq_of_finiteFlat_level.lean

import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsLocalRing

theorem GaloisRepAdic.iSup_map_levelAction_sub_id_inf_eq_of_finiteFlat_level
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpA : (p : A) ∈ maximalIdeal A)
    (I : Ideal A) [Finite (A ⧸ I)]
    (hfl : ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧
      Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          (ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))),
        (∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) → e g = ρ.levelAction I σ (e f))
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (N : Submodule A (ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))))
    (hN : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, N.map (ρ.levelAction I σ) ≤ N) :
    (⨆ σ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.levelAction I σ - LinearMap.id)) ⊓ N =
      ⨆ σ ∈ P.inertiaSubgroupIn ℚ, N.map (ρ.levelAction I σ - LinearMap.id) := by sorry
