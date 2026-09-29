-- Prove2me | Theorems.Thm_HopfAlgebra_exists_additive_eigenfunctional_tameCharacter_pow_of_finite_flat_of_inertiaSimple_step
-- name    : HopfAlgebra.exists_additive_eigenfunctional_tameCharacter_pow_of_finite_flat_of_inertiaSimple_step
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/d0edf29f-f075-5149-9237-3e92e3702469
-- title:
--   Raynaud digit bound for one inertia-simple step, functional form
-- statement:
--   Let $p$ be an odd prime and let $H$ be a commutative ring carrying a cocommutative Hopf algebra structure over the subring $\mathbb{Z}_{(p)} =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $p$, with $H$ finite and flat as a $\mathbb{Z}_{(p)}$-module. Write $M$ for the monoid `WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)` of $\overline{\mathbb{Q}}$-points of $H$ under convolution, and assume $f^p = 1$ for every $f \in M$. Let $P$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with $p$ a nonunit of $P$, and let $I_P$ denote `P.inertiaSubgroupIn ℚ`, the image in $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of the inertia subgroup of the decomposition subgroup of $P$. Let $K \le K'$ be submonoids of $M$, each stable under $I_P$ in the sense that whenever $\sigma \in I_P$, $f$ lies in the submonoid and $g \in M$ satisfies $g(h) = \sigma(f(h))$ for all $h \in H$, then $g$ lies in the submonoid; assume further that any submonoid $S$ with $K \le S \le K'$ and the same $I_P$-stability property equals $K$ or $K'$. Let $s \ge 1$ with $\#K' = p^{s}\,\#K$ (cardinalities as `Nat.card`). Then for every $\pi' \in \overline{\mathbb{Q}}$ with $\pi'^{\,p^{s}-1} = p$ there are a finite set $D \subseteq \mathbb{N}$ with every $j \in D$ satisfying $j < s$, and a function $L$ from $M$ to the residue field of $P$, such that $L(fg) = L(f) + L(g)$ for all $f, g \in K'$, $L$ vanishes on $K$, $L$ is nonzero at some element of $K'$, and for all $\sigma \in I_P$, all $f \in K'$ and all $g \in M$ with $g(h) = \sigma(f(h))$ for all $h \in H$ one has $L(g) = \theta(\sigma)^{\sum_{j \in D} p^{j}} L(f)$, where $\theta(\sigma) =$ `P.tameCharacter π' σ` is the residue of $\sigma(\pi')/\pi'$ when that quotient lies in $P$ and $0$ otherwise.
--
--   This is Raynaud's description of the tame inertia action on a simple finite flat group scheme of exponent $p$ over $\mathbb{Z}_{(p)}$ (absolute ramification index $1$), applied to a single inertia-simple step $K \le K'$ and phrased via an additive eigenfunctional into the residue field rather than an eigenvector: the exponent of the level-$s$ tame character has $p$-adic digits $0$ or $1$, recorded by the digit set $D \subseteq \{0, \dots, s-1\}$. It feeds the companion eigenvector form [`HopfAlgebra.exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat_of_inertiaSimple_step`](thm.html#HopfAlgebra.exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat_of_inertiaSimple_step).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_additive_eigenfunctional_tameCharacter_pow_of_finite_flat_of_inertiaSimple_step.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.exists_additive_eigenfunctional_tameCharacter_pow_of_finite_flat_of_inertiaSimple_step
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H : Type} [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (hMp : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), f ^ p = 1)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
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
    (s : ℕ) (hs : 1 ≤ s) (hcard : Nat.card K' = p ^ s * Nat.card K) :
    ∀ π' : AlgebraicClosure ℚ, π' ^ (p ^ s - 1) = p →
      ∃ D : Finset ℕ, (∀ j ∈ D, j < s) ∧
        ∃ L : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → IsLocalRing.ResidueField P,
        (∀ f ∈ K', ∀ g ∈ K', L (f * g) = L f + L g) ∧ (∀ f ∈ K, L f = 0) ∧ (∃ f ∈ K', L f ≠ 0) ∧
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
          ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
            (∀ h : H, g h = σ (f h)) → L g = P.tameCharacter π' σ ^ (∑ j ∈ D, p ^ j) * L f := by sorry
