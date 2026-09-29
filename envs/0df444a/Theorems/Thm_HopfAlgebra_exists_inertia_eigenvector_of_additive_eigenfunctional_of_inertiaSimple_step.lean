-- Prove2me | Theorems.Thm_HopfAlgebra_exists_inertia_eigenvector_of_additive_eigenfunctional_of_inertiaSimple_step
-- name    : HopfAlgebra.exists_inertia_eigenvector_of_additive_eigenfunctional_of_inertiaSimple_step
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/1053085c-1137-5417-bf1e-4b18475adf1c
-- title:
--   Inertia eigenvector from a tame eigenfunctional on a simple step
-- statement:
--   Let $p$ be an odd prime and let $\mathbb{Z}_{(p)}$ be the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ of rationals whose denominator is coprime to $p$. Let $H$ be a commutative ring carrying a $\mathbb{Z}_{(p)}$-Hopf algebra structure which is module-finite and flat over $\mathbb{Z}_{(p)}$ and cocommutative, and write $M$ for the monoid `WithConv` of $\mathbb{Z}_{(p)}$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$ under convolution; assume $f^p = 1$ for every $f \in M$. Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $P$, let $k_P$ be its residue field, and let $I_P =$ `P.inertiaSubgroupIn ℚ` be the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of the decomposition subgroup of $P$. Let $N$ be a $k_P$-vector space and $\mathrm{act}$ an arbitrary function assigning to each $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ a $k_P$-linear endomorphism of $N$. Let $F : M \to N$ satisfy $F(fg) = F(f)+F(g)$ and, for $\sigma \in I_P$, $F(g) = \mathrm{act}\,\sigma\,(F(f))$ whenever $g(h) = \sigma(f(h))$ for all $h \in H$. Let $K \le K'$ be submonoids of $M$, each closed under the twisting $f \mapsto \sigma \circ f$ by $\sigma \in I_P$, such that every $I_P$-stable submonoid $S$ with $K \le S \le K'$ equals $K$ or $K'$; assume $\mathrm{card}\,K' = p^s\,\mathrm{card}\,K$ for some $s \ge 1$, that $F$ vanishes on $K$ and is nonzero at some element of $K'$. Let $\pi' \in \overline{\mathbb{Q}}$ satisfy $\pi'^{\,p^s-1} = p$, and let $\theta =$ `P.tameCharacter π'` be the map sending $\sigma$ to the residue of $\sigma(\pi')/\pi'$ when this lies in $P$ and to $0$ otherwise. Finally let $D_0$ be a finite set of naturals all $< s$ and let $L : M \to k_P$ be additive on $K'$ (i.e. $L(fg) = L(f)+L(g)$ for $f, g \in K'$), zero on $K$, nonzero at some element of $K'$, and satisfy $L(g) = \theta(\sigma)^{\sum_{j \in D_0} p^j} L(f)$ for $\sigma \in I_P$, $f \in K'$ and $g$ the twist of $f$ by $\sigma$. The conclusion is that there exist a finite set $D$ of naturals all $< s$ and a nonzero $w \in N$ with $\mathrm{act}\,\sigma\,(w) = \theta(\sigma)^{\sum_{j \in D} p^j} \cdot w$ for all $\sigma \in I_P$; the digit set $D$ produced need not be $D_0$.
--
--   This is the eigenvector-extraction half, phrased purely in terms of monoids and additive functionals, of Raynaud's description of the action of tame inertia on a simple finite flat group scheme killed by $p$: from a tame eigenfunctional $L$ on an inertia-simple step $K \le K'$ one produces an eigenvector in $N$ whose eigencharacter is again a power of the tame character with $p$-power-digit exponent. It is combined with the companion construction of the eigenfunctional to prove [`HopfAlgebra.exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat_of_inertiaSimple_step`](thm.html#HopfAlgebra.exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat_of_inertiaSimple_step), the step used in the analysis of the local behaviour at $p$ of the representations attached to finite flat group schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_inertia_eigenvector_of_additive_eigenfunctional_of_inertiaSimple_step.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.exists_inertia_eigenvector_of_additive_eigenfunctional_of_inertiaSimple_step
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
    (hFK : ∀ f ∈ K, F f = 0) (hFK' : ∃ f ∈ K', F f ≠ 0)
    (π' : AlgebraicClosure ℚ) (hπ' : π' ^ (p ^ s - 1) = p)
    (D₀ : Finset ℕ) (hD₀ : ∀ j ∈ D₀, j < s)
    (L : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → IsLocalRing.ResidueField P)
    (hLmul : ∀ f ∈ K', ∀ g ∈ K', L (f * g) = L f + L g) (hLK : ∀ f ∈ K, L f = 0)
    (hLK' : ∃ f ∈ K', L f ≠ 0)
    (hLeig : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → L g = P.tameCharacter π' σ ^ (∑ j ∈ D₀, p ^ j) * L f) :
    ∃ D : Finset ℕ, (∀ j ∈ D, j < s) ∧ ∃ w : N, w ≠ 0 ∧
      ∀ σ ∈ P.inertiaSubgroupIn ℚ,
        act σ w = P.tameCharacter π' σ ^ (∑ j ∈ D, p ^ j) • w := by sorry
