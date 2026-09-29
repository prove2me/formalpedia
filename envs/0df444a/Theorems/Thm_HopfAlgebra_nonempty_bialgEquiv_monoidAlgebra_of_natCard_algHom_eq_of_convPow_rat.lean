-- Prove2me | Theorems.Thm_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat
-- name    : HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/9d1682db-1753-59a9-b82e-a4a899170f42
-- title:
--   Finite Hopf ℚ-algebra with cyclotomic q-point action is ℚ[ℤ/q]
-- statement:
--   Let $q$ be a prime and let $A$ be a commutative ring equipped with a Hopf algebra structure over $\mathbb{Q}$ that is finite as a $\mathbb{Q}$-module. Two hypotheses are imposed. First, the number of $\mathbb{Q}$-algebra homomorphisms $A \to \overline{\mathbb{Q}}$, where $\overline{\mathbb{Q}}$ is Mathlib's algebraic closure of $\mathbb{Q}$, is exactly $q$ as a natural cardinality. Second, for every ring automorphism $\sigma$ of $\overline{\mathbb{Q}}$ and every natural number $n_\sigma$ such that $\sigma(\zeta) = \zeta^{n_\sigma}$ for all $\zeta \in \overline{\mathbb{Q}}$ with $\zeta^q = 1$, one has, for every $\mathbb{Q}$-algebra homomorphism $\psi \colon A \to \overline{\mathbb{Q}}$ and every $a \in A$, the identity $\sigma(\psi(a)) = \psi^{*n_\sigma}(a)$, where $\psi^{*n_\sigma}$ denotes the $n_\sigma$-th power of $\psi$ for the convolution monoid structure on $A \to_{\mathbb{Q}} \overline{\mathbb{Q}}$ coming from the Hopf structure (transported through `WithConv`). The conclusion is that the type of $\mathbb{Q}$-bialgebra isomorphisms from $A$ to the monoid algebra $\mathbb{Q}[\mathrm{Multiplicative}(\mathbb{Z}/q)]$, i.e. the group algebra of the cyclic group of order $q$, is nonempty.
--
--   Dually, this says that a finite group scheme over $\mathbb{Q}$ with exactly $q$ geometric points on which the Galois action is through the mod-$q$ cyclotomic character is isomorphic to $\mu_q$; the proof invokes Cartier's theorem in the form [`HopfAlgebra.isReduced_of_finiteType_of_charZero`](thm.html#HopfAlgebra.isReduced_of_finiteType_of_charZero), that a Hopf algebra of finite type over a field of characteristic zero is reduced. It feeds the classification of group schemes of prime order used in the project, being cited by [`HopfAlgebra.prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two`](thm.html#HopfAlgebra.prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat
    (q : ℕ) [Fact q.Prime]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A] [Module.Finite ℚ A]
    (hgenq : Nat.card (A →ₐ[ℚ] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (nσ : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (ψ : A →ₐ[ℚ] AlgebraicClosure ℚ) (a : A),
        σ (ψ a) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) a) :
    Nonempty (A ≃ₐc[ℚ] MonoidAlgebra ℚ (Multiplicative (ZMod q))) := by sorry
