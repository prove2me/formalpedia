-- Prove2me | Theorems.Thm_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_ne_two
-- name    : HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/ad8dc6d9-07f9-5b24-84ba-228e7caf6f0b
-- title:
--   Oort–Tate over ℤ: cyclotomic points give ℤ[ℤ/q]
-- statement:
--   Let $q$ be a prime with $q \neq 2$, and let $K$ be a commutative ring carrying a Hopf algebra structure over $\mathbf Z$ that is finite and flat as a $\mathbf Z$-module. Assume two conditions. First, the number of $\mathbf Z$-algebra homomorphisms $K \to \overline{\mathbf Q}$ (for the chosen algebraic closure `AlgebraicClosure ℚ`) is exactly $q$. Second, the Galois action on these points is cyclotomic in the following sense: for every ring automorphism $\sigma$ of $\overline{\mathbf Q}$ and every natural number $n_\sigma$ such that $\sigma(\zeta) = \zeta^{n_\sigma}$ for all $\zeta \in \overline{\mathbf Q}$ with $\zeta^q = 1$, one has, for every $\psi \in \operatorname{Hom}_{\mathbf Z\text{-alg}}(K, \overline{\mathbf Q})$ and every $k \in K$, the identity $\sigma(\psi(k)) = \psi^{\ast n_\sigma}(k)$, where $\psi^{\ast n_\sigma}$ denotes the $n_\sigma$-th power of $\psi$ in the convolution monoid structure on algebra homomorphisms (transported through `WithConv`). The conclusion is that the type of $\mathbf Z$-bialgebra isomorphisms $K \simeq \mathbf Z[\operatorname{Multiplicative}(\mathbf Z/q)]$ is nonempty, i.e. $K$ is isomorphic as a $\mathbf Z$-bialgebra to the group algebra of $\mathbf Z/q$ over $\mathbf Z$.
--
--   This is the multiplicative case of the Oort–Tate classification of group schemes of prime order over $\mathbf Z$: the hypotheses say that $\operatorname{Spec} K$ is a finite flat group scheme over $\mathbf Z$ whose geometric points form a cyclic group of order $q$ permuted by the mod-$q$ cyclotomic character, and the conclusion identifies it with $\mu_q$. It is used in the analysis of sections of finite flat group schemes whose convolution powers are trivial, where the odd-order multiplicative layer models must be recognised as Kummer-type extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_ne_two.lean

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.RingTheory.Bialgebra.Equiv
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.MonoidAlgebra.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_ne_two
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Module.Finite ℤ K] [Module.Flat ℤ K]
    (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (nσ : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ) (k : K),
        σ (ψ k) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) k) :
    Nonempty (K ≃ₐc[ℤ] MonoidAlgebra ℤ (Multiplicative (ZMod q))) := by sorry
