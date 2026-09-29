-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_exists_monic_eval2_inv_div_pow_eq_zero_and_map_eq_X_pow_mul_X_sub_one
-- name    : ModularCurve.ModularPolynomialData.exists_monic_eval2_inv_div_pow_eq_zero_and_map_eq_X_pow_mul_X_sub_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/da6ca4f5-b10c-5da6-baf1-ca8e6648746a
-- title:
--   Reversed modular polynomial at a prime and its reduction
-- statement:
--   Let $p$ be a natural number, assumed prime, and let `data` be a `ModularPolynomialData p`: a polynomial $\Phi \in \mathbb{Z}[X][Y]$ together with the data that $\Phi$ is monic in $Y$, that its degree in $Y$ equals $\mathrm{dedekindPsi}\,p = \sum_{d \mid p,\ d \text{ squarefree}} p/d$ (which is $p+1$ for $p$ prime), and that $\Phi$ vanishes when $X$ is specialised to the $q$-expansion of $j$ (via the ring homomorphism `evalAtJ` from $\mathbb{Z}[X]$ to Laurent series over $\mathbb{Q}$) and $Y$ to `jqN p`. The assertion is the existence of a polynomial $Q \in \mathbb{Z}[X][Y]$ which is monic in $Y$ of degree exactly $p+1$ and has the following two properties. First, for every field $S$ and all $x, y \in S$ with $x \neq 0$, if $\Phi(x,y) = 0$ — evaluation of $\Phi$ at $Y \mapsto y$ using the homomorphism $\mathbb{Z}[X] \to S$, $X \mapsto x$ — then $Q(x^{-1}, y/x^{p}) = 0$. Second, for every commutative ring $R$ of characteristic $p$, applying to the coefficients of $Q$ the homomorphism $\mathbb{Z}[X] \to R$ with $X \mapsto 0$ gives $Y^{p}(Y-1)$ in $R[Y]$.
--
--   This is the reversed (normalised) modular polynomial of prime level: $Q(u,T)$ is, up to the stated coefficient bound, $u^{p(p+1)}\Phi_p(1/u, T/u^{p})$, so it exhibits the cusp coordinate $j(q^{p})/j^{p}$ as satisfying a monic equation of degree $p+1$ over $\mathbb{Z}[1/j]$, while its reduction modulo $p$ is $T^{p}(T-1)$, a form of Kronecker's congruence $\Phi_p \equiv (X^{p}-Y)(X-Y^{p}) \bmod p$. It is used in the analysis of the charts at the cusp $\infty$, namely in [`ModularCurve.JHPlaceSpecialization.ProlongationDatum.mem_integers_and_residue_mem_and_mem_of_mem_cuspChartSetInf`](thm.html#ModularCurve.JHPlaceSpecialization.ProlongationDatum.mem_integers_and_residue_mem_and_mem_of_mem_cuspChartSetInf) and [`ModularCurve.XHDRModelAtP.chartEtaleAt_cuspChartSetInf_of_isInftySide_prolongationDatum`](thm.html#ModularCurve.XHDRModelAtP.chartEtaleAt_cuspChartSetInf_of_isInftySide_prolongationDatum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_exists_monic_eval2_inv_div_pow_eq_zero_and_map_eq_X_pow_mul_X_sub_one.lean

import Mathlib
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial ModularCurve

theorem ModularCurve.ModularPolynomialData.exists_monic_eval2_inv_div_pow_eq_zero_and_map_eq_X_pow_mul_X_sub_one
    (p : ℕ) [Fact p.Prime] (data : ModularPolynomialData p) :
    ∃ Q : Polynomial (Polynomial ℤ), Q.Monic ∧ Q.natDegree = p + 1 ∧
      (∀ (S : Type*) [Field S] (x y : S), x ≠ 0 →
          data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom S) x) y = 0 →
          Q.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom S) x⁻¹) (y / x ^ p) = 0) ∧
      (∀ (R : Type*) [CommRing R] [CharP R p],
          Q.map (Polynomial.eval₂RingHom (Int.castRingHom R) 0) = Polynomial.X ^ p * (Polynomial.X - 1)) := by sorry
