-- Prove2me | Theorems.Thm_HopfAlgebra_exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat_of_inertiaSimple_step
-- name    : HopfAlgebra.exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat_of_inertiaSimple_step
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/43097eb5-f96d-5c8f-b6ca-71c8457e08e1
-- title:
--   Raynaud digit bound for one inertia-simple step
-- statement:
--   Let $p$ be an odd prime and let $H$ be a commutative ring carrying the structure of a Hopf algebra over the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $p$ (i.e. $\mathbb{Z}_{(p)}$), with $H$ finite and flat as a module over that subring and with cocommutative comultiplication. Write $M$ for the monoid `WithConv` of $\mathbb{Z}_{(p)}$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$ under convolution, and assume $f^p = 1$ for every $f \in M$. Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ lying in the nonunits of $P$, and let $I_P$ denote `P.inertiaSubgroupIn ℚ`, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $P$ inside its decomposition subgroup. Let $N$ be a module over the residue field $k_P$ of $P$, let $\sigma \mapsto \mathrm{act}\,\sigma$ assign to each element of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ a $k_P$-linear endomorphism of $N$, and let $F : M \to N$ satisfy $F(fg) = F(f) + F(g)$ and the equivariance condition that $F(g) = \mathrm{act}\,\sigma\,(F(f))$ whenever $\sigma \in I_P$ and $g(h) = \sigma(f(h))$ for all $h \in H$. Let $K \le K'$ be submonoids of $M$, each stable in the sense that if $\sigma \in I_P$, $f$ lies in the submonoid and $g(h) = \sigma(f(h))$ for all $h$, then $g$ lies in the submonoid; assume that every such $I_P$-stable submonoid $S$ with $K \le S \le K'$ equals $K$ or $K'$. Assume further $s \ge 1$ with $\#K' = p^s\,\#K$ (cardinalities as natural numbers), that $F$ vanishes on $K$, and that $F$ is nonzero at some element of $K'$. The conclusion is that for every $\pi' \in \overline{\mathbb{Q}}$ with $\pi'^{\,p^s-1} = p$ there exist a finite set $D \subseteq \mathbb{N}$ all of whose elements are $< s$ and a nonzero $w \in N$ with $\mathrm{act}\,\sigma\,(w) = \theta_{\pi'}(\sigma)^{\sum_{j \in D} p^j}\, w$ for all $\sigma \in I_P$, where $\theta_{\pi'}(\sigma)$ is `P.tameCharacter π' σ`, the residue of $\sigma(\pi')/\pi'$ in $k_P$ when that ratio lies in $P$, and $0$ otherwise.
--
--   This is Raynaud's description of the action of tame inertia on a single inertia-simple step $K'/K$ of the $\overline{\mathbb{Q}}$-points of a finite flat commutative group scheme of exponent $p$ over $\mathbb{Z}_{(p)}$ (absolute ramification $e = 1$): the action is through a product of fundamental characters of level $s$ with exponents $0$ or $1$. It feeds the corresponding statement for a Galois-simple step with nonvanishing reduction-kernel functional, used in the analysis of the local behaviour at $p$ of the mod $p$ representations attached to the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat_of_inertiaSimple_step.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat_of_inertiaSimple_step
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
    (K K' : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)))
    (hKK' : K ≤ K')
    (hK : (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K,
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g ∈ K))
    (hK' : (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g ∈ K'))
    (hstep : ∀ S : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      K ≤ S → S ≤ K' →
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ S,
        ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          (∀ h : H, g h = σ (f h)) → g ∈ S) →
      S = K ∨ S = K')
    (s : ℕ) (hs : 1 ≤ s) (hcard : Nat.card K' = p ^ s * Nat.card K)
    (hFK : ∀ f ∈ K, F f = 0) (hFK' : ∃ f ∈ K', F f ≠ 0) :
    ∀ π' : AlgebraicClosure ℚ, π' ^ (p ^ s - 1) = p →
      ∃ D : Finset ℕ, (∀ j ∈ D, j < s) ∧ ∃ w : N, w ≠ 0 ∧
        ∀ σ ∈ P.inertiaSubgroupIn ℚ,
          act σ w = P.tameCharacter π' σ ^ (∑ j ∈ D, p ^ j) • w := by sorry
