-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_exists_tangent_eq_and_coeff_subst_eq_ghost_of_log
-- name    : MvFormalGroup.CartierModule.exists_tangent_eq_and_coeff_subst_eq_ghost_of_log
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/e1c99868-303d-58db-8682-975bd60557b8
-- title:
--   Cartier module elements with prescribed ghost logarithm
-- statement:
--   Let $p$ be a prime, $\mathcal O$ a commutative ring, $d$ a natural number, and let $\Phi$ be a $d$-dimensional formal group law over $\mathcal O$, i.e. a $d$-tuple of power series in the variables indexed by $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$ with vanishing constant terms, whose linear coefficients in each group of variables are the identity matrix and which satisfies the associativity identity, and assume $\Phi$ is commutative in the sense that interchanging the two groups of variables fixes each component. Let $f, \psi : \mathrm{Fin}\,d \to \mathcal O[[X_0,\dots,X_{d-1}]]$ be tuples with vanishing constant terms such that the coefficient of $X_j$ in $f_i$ is $1$ if $i = j$ and $0$ otherwise, which are mutually inverse under substitution ($f_i(\psi) = X_i$ and $\psi_i(f) = X_i$ for all $i$), and such that $f$ is a logarithm for $\Phi$: $f_i(\Phi(X,Y)) = f_i(X) + f_i(Y)$ for every $i$, as power series in the variables indexed by $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$. Let $c : \mathbb N \to \mathrm{Fin}\,d \to \mathcal O$ be arbitrary. Then there exists an element $m$ of the Cartier module of $\Phi$ at $p$, that is, a $d$-tuple $m_j \in \mathcal O[[X_k : k \in \mathbb N]]$ with vanishing constant terms satisfying $m_j(\mathrm{addFam}\,p\,\mathcal O) = \Phi_j\big(m(X_{0,\bullet}), m(X_{1,\bullet})\big)$, where $\mathrm{addFam}\,p\,\mathcal O$ is the family of Witt addition polynomials $\mathrm{wittAdd}$ over $\mathcal O$ in the variables indexed by $\mathrm{Fin}\,2 \times \mathbb N$, such that: the tangent vector of $m$, the tuple of coefficients of $X_0$ in the $m_j$, is $(c\,0\,j)_j$; for all $j$ and all $k, n \in \mathbb N$ the coefficient of $X_k^{p^n}$ in $f_j(m)$ equals $p^k \, c\,(k+n)\,j$; and for every exponent multiset $e$ which is not of the form $X_k^{p^n}$ the corresponding coefficient of $f_j(m)$ vanishes.
--
--   Classically this constructs, from the ghost-coordinate data $c$, a homomorphism from the $p$-typical Witt formal group to a commutative formal group law $\Phi$ equipped with a normalised logarithm $f$, the logarithm of the homomorphism being $\sum_N c_N(j) w_N$ for the ghost polynomials $w_N = \sum_{k \le N} p^k X_k^{p^{N-k}}$. It is used in the construction of a basis of curves for the Cartier module of such a law, via [`MvFormalGroup.exists_cartierModule_vBasis_mvPolynomial_X_of_log`](thm.html#MvFormalGroup.exists_cartierModule_vBasis_mvPolynomial_X_of_log), and relies on the additivity of the ghost components for Witt addition recorded in [`MvFormalGroup.WittLaw.subst_addFam_eq_add_of_coeff_eq_ghost`](thm.html#MvFormalGroup.WittLaw.subst_addFam_eq_add_of_coeff_eq_ghost).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_exists_tangent_eq_and_coeff_subst_eq_ghost_of_log.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u
open MvPowerSeries in

theorem MvFormalGroup.CartierModule.exists_tangent_eq_and_coeff_subst_eq_ghost_of_log
    (p : ℕ) [Fact p.Prime] {𝓞 : Type u} [CommRing 𝓞] {d : ℕ}
    (Φ : MvFormalGroup d 𝓞) [Φ.IsComm]
    (f ψ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hf0 : ∀ i, (f i).constantCoeff = 0)
    (hf1 : ∀ i j : Fin d, (coeff (Finsupp.single j 1) (f i) : 𝓞) = if i = j then 1 else 0)
    (hψ0 : ∀ i, (ψ i).constantCoeff = 0)
    (hfψ : ∀ i, subst ψ (f i) = X i) (hψf : ∀ i, subst f (ψ i) = X i)
    (hlog : ∀ i, subst Φ.toPowerSeries (f i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (f i) +
        subst (fun j => X (Sum.inr j)) (f i))
    (c : ℕ → Fin d → 𝓞) :
    ∃ m : MvFormalGroup.CartierModule p Φ,
      (∀ j, MvFormalGroup.CartierModule.tangent m j = c 0 j) ∧
      (∀ (j : Fin d) (k n : ℕ),
        (coeff (Finsupp.single k (p ^ n)) (subst m.toPowerSeries (f j)) : 𝓞) = (p : 𝓞) ^ k * c (k + n) j) ∧
      (∀ (j : Fin d) (e : ℕ →₀ ℕ), (∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) →
        (coeff e (subst m.toPowerSeries (f j)) : 𝓞) = 0) := by sorry
