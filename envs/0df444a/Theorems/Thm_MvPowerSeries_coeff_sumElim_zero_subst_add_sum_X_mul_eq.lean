-- Prove2me | Theorems.Thm_MvPowerSeries_coeff_sumElim_zero_subst_add_sum_X_mul_eq
-- name    : MvPowerSeries.coeff_sumElim_zero_subst_add_sum_X_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/45d1da1a-ce0c-57fc-81d1-a6cbade7b00b
-- title:
--   Coefficient of Y⁰ in f(A+YB) equals f(A)
-- statement:
--   Let $R$ be a commutative ring, let $\sigma$ and $\kappa$ be finite types and $\tau$ an arbitrary type. Let $f$ be a multivariate power series in the variables indexed by $\sigma$ over $R$, let $A : \sigma \to R[[X_\tau]]$ be a family of power series in the variables indexed by $\tau$ whose constant coefficients all vanish, let $B : \sigma \times \kappa \to R[[X_\tau]]$ be an arbitrary family, and let $m : \tau \to_{\mathrm{f}} \mathbb{N}$ be a multi-index in the $\tau$-variables. Form, for each $i \in \sigma$, the power series in the variables indexed by $\tau \oplus \kappa$ given by $A_i$ rewritten in the variables $X_{\mathrm{inl}\,t}$ ($t \in \tau$), plus $\sum_{k' \in \kappa} X_{\mathrm{inr}\,k'} \cdot B_{i k'}$, where $B_{ik'}$ is likewise rewritten in the variables $X_{\mathrm{inl}\,t}$. The assertion is that the coefficient of the substitution of this family into $f$, at the multi-index on $\tau \oplus \kappa$ which is $m$ on the $\tau$-summand and $0$ on the $\kappa$-summand, equals the coefficient of $X^m$ in the substitution of $A$ into $f$. The vanishing of the constant coefficients of the $A_i$ is what makes the substitutions in question legitimate.
--
--   This is the order-zero part of the Taylor expansion of a substitution: writing $G_i = A_i(X) + \sum_k Y_k B_{ik}(X)$, the part of $f(G)$ of degree $0$ in the variables $Y$ is $f(A)$. It is used, alongside the computation of the part linear in $Y$, in the formal-group development: in the construction of a substitution realising a homomorphism under a non-divisibility hypothesis, in the congruence satisfied by truncated scaled logarithms, and in the identity expressing $f(A + \sum_k Y_k B_{\cdot k})$ through the partial derivatives of $f$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPowerSeries_coeff_sumElim_zero_subst_add_sum_X_mul_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w x

theorem MvPowerSeries.coeff_sumElim_zero_subst_add_sum_X_mul_eq
    {R : Type u} [CommRing R] {σ : Type v} [Fintype σ] {τ : Type w} {κ : Type x} [Fintype κ]
    (f : MvPowerSeries σ R)
    (A : σ → MvPowerSeries τ R) (hA : ∀ i, MvPowerSeries.constantCoeff (A i) = 0)
    (B : σ → κ → MvPowerSeries τ R) (m : τ →₀ ℕ) :
    MvPowerSeries.coeff (m.sumElim 0)
        (MvPowerSeries.subst
          (fun i => MvPowerSeries.subst (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (τ ⊕ κ) R)) (A i) +
            ∑ k' : κ, MvPowerSeries.X (Sum.inr k') *
              MvPowerSeries.subst (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (τ ⊕ κ) R)) (B i k'))
          f) =
      MvPowerSeries.coeff m (MvPowerSeries.subst A f) := by sorry
