-- Prove2me | Theorems.Thm_MvFormalGroup_cartierDual_pow_apply_eq_finsum_coeff_subst_mul_apply_pow
-- name    : MvFormalGroup.cartierDual_pow_apply_eq_finsum_coeff_subst_mul_apply_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/327fe72d-8cad-59b3-a6f0-c09311235491
-- title:
--   Frobenius on the Cartier dual is dual to Verschiebung
-- statement:
--   Let $k$ be a field of characteristic $p$, with $p$ prime, and let $F$ be an $n$-dimensional formal group law over $k$: an $n$-tuple `F.toPowerSeries` of power series in the two blocks of variables $X_{\mathrm{inl}\,j}, X_{\mathrm{inr}\,j}$ with vanishing constant terms, linear coefficients $\delta_{ij}$ in each block, and the associativity identity; the instance `F.IsComm` asserts that interchanging the two blocks fixes each $F_i$. Let $V_1,\dots,V_n \in k[[X_1,\dots,X_n]]$ have zero constant term and satisfy $V_i(X_1^p,\dots,X_n^p) = ([p]_F)_i$, where $[p]_F$ is the $p$-th iterate `F.nthSeries p` defined by $0$-tuple at $0$ and $(m+1)$-st iterate $F(\,m\text{-th iterate}(X), X)$. Let $L$ be a commutative Hopf algebra over $k$, finite as a $k$-module, let $\pi : k[[X_1,\dots,X_n]] \to L$ and $\Theta : k[[X,Y]] \to L \otimes_k L$ be $k$-algebra maps with $\Theta(G(X)) = \pi(G)\otimes 1$ and $\Theta(G(Y)) = 1 \otimes \pi(G)$ for all $G$, with comultiplication $\Delta(\pi G) = \Theta(G(F(X,Y)))$ and counit $\varepsilon(\pi G) = G(0)$. Then for every $\varphi$ in the Cartier dual [`CartierDual k L`](def/HopfAlgebra_CartierDual.html#L12), that is every $k$-linear form on $L$, with $\varphi^p$ its $p$-th power there, and every $g \in k[[X_1,\dots,X_n]]$, $$\varphi^p(\pi g) = \sum_{a \in \mathbb{N}^n} \mathrm{coeff}_a\big(g(V(X))\big)\,\varphi(\pi(X^a))^p,$$ the right-hand side being an unrestricted finsum over all multi-indices $a$.
--
--   This is the statement that the Frobenius endomorphism $\varphi \mapsto \varphi^p$ of the Cartier dual of a finite subgroup scheme of a commutative formal group in characteristic $p$ is dual to the Verschiebung, computed in coordinates by substitution of the series $V$ with $[p]_F(X) = V(X^p)$. It feeds the bound [`MvFormalGroup.finrank_primitives_add_le_of_ker_eq_span_nthSeries_of_finrank_eq_pow`](thm.html#MvFormalGroup.finrank_primitives_add_le_of_ker_eq_span_nthSeries_of_finrank_eq_pow) on the rank of the space of primitive elements for such a subgroup scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_cartierDual_pow_apply_eq_finsum_coeff_subst_mul_apply_pow.lean

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open scoped TensorProduct

theorem MvFormalGroup.cartierDual_pow_apply_eq_finsum_coeff_subst_mul_apply_pow
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {n : ℕ} (F : MvFormalGroup n k) [F.IsComm]
    (V : Fin n → MvPowerSeries (Fin n) k) (hV0 : ∀ i, MvPowerSeries.constantCoeff (V i) = 0)
    (hV : ∀ i, MvPowerSeries.subst (fun l => (MvPowerSeries.X l : MvPowerSeries (Fin n) k) ^ p) (V i) =
      F.nthSeries p i)
    {L : Type v} [CommRing L] [HopfAlgebra k L] [Module.Finite k L]
    (π : MvPowerSeries (Fin n) k →ₐ[k] L)
    (Θ : MvPowerSeries (Fin n ⊕ Fin n) k →ₐ[k] L ⊗[k] L)
    (hΘl : ∀ G : MvPowerSeries (Fin n) k, Θ (MvPowerSeries.subst
      (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) G) = π G ⊗ₜ[k] 1)
    (hΘr : ∀ G : MvPowerSeries (Fin n) k, Θ (MvPowerSeries.subst
      (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) G) = 1 ⊗ₜ[k] π G)
    (hcomul : ∀ G, Coalgebra.comul (R := k) (π G) = Θ (MvPowerSeries.subst F.toPowerSeries G))
    (hcounit : ∀ G, Coalgebra.counit (R := k) (π G) = MvPowerSeries.constantCoeff G)
    (φ : CartierDual k L) (g : MvPowerSeries (Fin n) k) :
    (φ ^ p) (π g) = ∑ᶠ a : Fin n →₀ ℕ,
      MvPowerSeries.coeff a (MvPowerSeries.subst V g) * φ (π (MvPowerSeries.monomial a (1 : k))) ^ p := by sorry
