-- Prove2me | Theorems.Thm_ModularCurve_sq_ne_add_one_sq_mul_of_joint_eigenvector_tateGenOpH_T_dia
-- name    : ModularCurve.sq_ne_add_one_sq_mul_of_joint_eigenvector_tateGenOpH_T_dia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/3ec03007-d634-57aa-a001-f1f2d322be46
-- title:
--   Joint Tₚ–⟨ d⟩ eigenvalues avoid a²=(p+1)²e
-- statement:
--   Fix a nonzero natural number $N$, a prime $p$ with $p \nmid N$, a subgroup $H \le (\mathbb{Z}/N)^\times$ and a set $S$ of naturals with $p \notin S$. Assume [`ModularCurve.HeckeDiamondInputsHAll N H`](def/ModularCurve_XHOperators.html#L113): for every prime $\ell$ the package `HeckeInputsHAlong` holds for $X_H(N)$ over $\overline{\mathbb{Q}}$ at $\ell$ (existence of the defining data for the correspondence maps $\alpha,\beta$, their integrality, principal divisors on the base-changed top function field, finiteness along $\alpha$, together with the fundamental identity for $\beta$ and the norm formula for $\alpha$), and for every $d \in (\mathbb{Z}/N)^\times$ there is an automorphism of the function field $\overline{\mathbb{Q}}\,$-base change of $X_H$ satisfying `IsDiamondAutHBar`, i.e. acting on ratios of $q$-expansions of modular forms of level $\Gamma_H(N)$ as slashing by a $\Gamma_0(N)$-matrix with upper-left entry $\equiv d$. Let $K$ be an algebraically closed field which is a $\mathbb{Z}_p$-algebra with injective structure map. Write $T = \mathrm{TateModule}\,p\,(J_H(N))$, the group of sequences $(x_n)$ in the degree-zero divisor class group of $X_H$ over $\overline{\mathbb{Q}}$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$, carrying the endomorphisms `tateGenOpH` induced by the Hecke operator at $p$ and by the diamond operator $\langle d\rangle$. If $v \in K \otimes_{\mathbb{Z}_p} T$ is nonzero and is an eigenvector of the base changes of these two endomorphisms with eigenvalues $a$ and $e$, then $a^2 \neq (\text{image of } p+1 \text{ in } K)^2 \cdot e$.
--
--   This is the numerical non-degeneracy input for the classical argument that an eigenvector on the $p$-adic Tate module of $J_H(N)$ cannot have $|a|^2 = (p+1)^2$, since $a$ is bounded by the Weil-type bound attached to $T_p$ while $e$ is a root of unity. It is used to supply the non-degeneracy hypothesis in the vanishing statement for classes in the Tate module of $J_1$ annihilated by the two degeneracy pushforwards, i.e. in the injectivity of the old part at level $Np$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_sq_ne_add_one_sq_mul_of_joint_eigenvector_tateGenOpH_T_dia.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem ModularCurve.sq_ne_add_one_sq_mul_of_joint_eigenvector_tateGenOpH_T_dia
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N) (H : Subgroup (ZMod N)ˣ)
    (S : Set ℕ) (hpS : p ∉ S)
    (hin : ModularCurve.HeckeDiamondInputsHAll N H)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra ℤ_[p] K] (hK : Function.Injective (algebraMap ℤ_[p] K))
    (v : K ⊗[ℤ_[p]] TateModule p (ModularCurve.JH N H)) (a e : K) (hv : v ≠ 0)
    (hA : (ModularCurve.tateGenOpH N H S p (.T p Fact.out hpS hpN)).baseChange K v = a • v)
    (d : (ZMod N)ˣ) (hD : (ModularCurve.tateGenOpH N H S p (.dia d)).baseChange K v = e • v) :
    a ^ 2 ≠ (algebraMap ℤ_[p] K ((p + 1 : ℕ) : ℤ_[p])) ^ 2 * e := by sorry
