-- Prove2me | Theorems.Thm_GaloisRepAdic_isFlatAt_of_forall_point_of_finite_index
-- name    : GaloisRepAdic.isFlatAt_of_forall_point_of_finite_index
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/88d52237-fc72-56d1-a714-f7e46fa67a91
-- title:
--   Flatness at p detected by finitely many bounded-index local points
-- statement:
--   Let $P$ be a commutative local ring, let $n$ be a natural number and let $A_i$, $i \in \mathrm{Fin}\,n$, be commutative local rings. Let $\chi_i : P \to A_i$ be ring homomorphisms, each local (non-units to non-units), jointly injective in the sense that $\chi_i(x)=0$ for all $i$ forces $x=0$. Let $p, c$ be natural numbers with the image of $p$ in $P$ lying in the maximal ideal of $P$, and assume the index bound: for every tuple $(a_i) \in \prod_i A_i$ there is $x \in P$ with $\chi_i(x) = p^c a_i$ for all $i$. Assume each $A_i/pA_i$ is finite. Let $\rho$ be an adic Galois representation over $P$, i.e. a free finite $P$-module $V$ of rank $2$ with a monoid homomorphism from $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ to $\mathrm{End}_P V$ that is continuous for the maximal-ideal-adic filtration (for each $m$ some finite extension $L/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ acts trivially modulo $\mathfrak{m}_P^m V$). Suppose that for each $i$ the base change $A_i \otimes_P V$ along $\chi_i$ is flat at $p$. Then $\rho$ is flat at $p$: the residue field of $P$ is finite and, for every ideal $I$ of $P$ with $P/I$ finite, there is a commutative ring $H$ that is a cocommutative Hopf algebra, module-finite and flat over the subring of $\mathbb{Q}$ of rationals with denominator coprime to $p$, together with a bijection from the convolution monoid of its $\overline{\mathbb{Q}}$-points onto $V/IV$ carrying products to sums and intertwining the Galois action on points with the induced action on $V/IV$.
--
--   This is the descent step for the property of being "flat at $p$" (finite-flatness, or goodness at $p$, of an adic Galois representation in the sense of Darmon–Diamond–Taylor §2.4): the property may be checked after base change along finitely many jointly injective local homomorphisms whose diagonal image contains $p^c$ times the product. It is used in the construction of Hecke Galois representations attached to cusp forms, in [`CuspForm.HeckeGaloisRepDatum.exists_pi_eq_and_isFlatAt_of_primeFactors_subset`](thm.html#CuspForm.HeckeGaloisRepDatum.exists_pi_eq_and_isFlatAt_of_primeFactors_subset).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isFlatAt_of_forall_point_of_finite_index.lean

import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

theorem GaloisRepAdic.isFlatAt_of_forall_point_of_finite_index
    {P : Type} [CommRing P] [IsLocalRing P] {n : ℕ} {A : Fin n → Type}
    [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
    (χ : ∀ i, P →+* A i) (hχ : ∀ i, IsLocalHom (χ i))
    (hinj : ∀ x, (∀ i, χ i x = 0) → x = 0)
    {p c : ℕ} (hpP : (p : P) ∈ IsLocalRing.maximalIdeal P)
    (hidx : ∀ a : ∀ i, A i, ∃ x : P, ∀ i, χ i x = (p : A i) ^ c * a i)
    (hAfin : ∀ i, Finite (A i ⧸ Ideal.span {(p : A i)}))
    (ρ : GaloisRepAdic P) (hflat : ∀ i, (ρ.baseChangeAlong (χ i) (hχ i)).IsFlatAt p) :
    ρ.IsFlatAt p := by sorry
