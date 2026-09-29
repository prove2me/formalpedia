-- Prove2me | Theorems.Thm_HopfAlgebra_exists_finiteFlat_galoisSimple_factor_of_nonzero_equivariant_map
-- name    : HopfAlgebra.exists_finiteFlat_galoisSimple_factor_of_nonzero_equivariant_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/50afbf16-8b85-531b-8fae-e3987722523d
-- title:
--   Galois-simple finite flat factor for nonzero inertia-equivariant maps
-- statement:
--   Let $p$ be an odd prime and write $R$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $p$. Let $H$ be a commutative ring carrying an $R$-Hopf algebra structure which is module-finite and flat over $R$ and whose comultiplication is cocommutative, and let `WithConv (H →ₐ[R] AlgebraicClosure ℚ)` denote the set of $R$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$ with its convolution monoid structure; assume every such point $f$ satisfies $f^p = 1$. Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $P$, and let $k$ be the residue field of $P$. Let $N$ be a $k$-vector space, let $\mathrm{act}$ assign to each $\sigma \in \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ a $k$-linear endomorphism of $N$ (no compatibility with the group law is assumed), and let $F$ be a map from the points of $H$ to $N$ with $F(fg) = F(f) + F(g)$, such that for every $\sigma$ in the inertia subgroup of $P$ over $\mathbb{Q}$ (the image in $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of the inertia subgroup inside the decomposition subgroup) and all points $f, g$ with $g(h) = \sigma(f(h))$ for all $h \in H$ one has $F(g) = \mathrm{act}(\sigma)(F(f))$; assume $F$ is not identically zero. The conclusion asserts the existence of a commutative ring $H'$ with an $R$-Hopf algebra structure that is again module-finite, flat and cocommutative over $R$, all of whose $\overline{\mathbb{Q}}$-points are killed by $p$, together with a map $F'$ from the points of $H'$ to the same $N$ satisfying the same three conditions (additivity for convolution, equivariance for the inertia subgroup of $P$ with the same $\mathrm{act}$, and non-vanishing at some point), and with the points of $H'$ Galois-simple: every submonoid $S$ of the convolution monoid of points of $H'$ such that $f \in S$ and $g(h) = \sigma(f(h))$ for all $h \in H'$ imply $g \in S$, for every $\sigma \in \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$, equals $\bot$ or $\top$.
--
--   This is the dévissage (Jordan–Hölder) step towards Raynaud's bound on the digits of tame inertia characters: it replaces a finite flat cocommutative Hopf algebra over $\mathbb{Z}_{(p)}$ with $p$-torsion points by one whose point group admits no proper nontrivial Galois-stable submonoid, while preserving a nonzero inertia-equivariant additive functional into a residue-field vector space. It is used in the proof of [`HopfAlgebra.exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat`](thm.html#HopfAlgebra.exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_finiteFlat_galoisSimple_factor_of_nonzero_equivariant_map.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.exists_finiteFlat_galoisSimple_factor_of_nonzero_equivariant_map
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H : Type} [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (hMp : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), f ^ p = 1)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (N : Type) [AddCommGroup N] [Module (IsLocalRing.ResidueField P) N]
    (act : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N →ₗ[IsLocalRing.ResidueField P] N)
    (F : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → N)
    (hFmul : ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      F (f * g) = F f + F g)
    (hFequiv : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → F g = act σ (F f))
    (hFne : ∃ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), F f ≠ 0) :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H'),
      Module.Finite (GaloisRep.ratLocalizedAt p) H' ∧
      Module.Flat (GaloisRep.ratLocalizedAt p) H' ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H' ∧
      (∀ f : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), f ^ p = 1) ∧
      ∃ F' : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → N,
        (∀ f g : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          F' (f * g) = F' f + F' g) ∧
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
          ∀ f g : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
            (∀ h : H', g h = σ (f h)) → F' g = act σ (F' f)) ∧
        (∃ f : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), F' f ≠ 0) ∧
        (∀ S : Submonoid (WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ f ∈ S,
            ∀ g : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
              (∀ h : H', g h = σ (f h)) → g ∈ S) →
          S = ⊥ ∨ S = ⊤) := by sorry
