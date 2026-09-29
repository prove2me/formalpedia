-- Prove2me | Theorems.Thm_ModularCurve_exists_pairing_family_pow_nsmul_eq_zero_galois_hecke_compat
-- name    : ModularCurve.exists_pairing_family_pow_nsmul_eq_zero_galois_hecke_compat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/c1d302e3-1430-5d77-9929-55a53a562e8a
-- title:
--   Compatible family of Weil pairings on J₀(N)[ℓ^k]
-- statement:
--   Fix a natural number $N \neq 0$ and a natural number $\ell \neq 0$ (no primality of $\ell$ is assumed). Write $J =$ `JZero N` for the group of degree-zero divisor classes of the modular function field of level $N$ base changed to $\overline{\mathbf Q}$, that is, the quotient of the degree-zero divisors of `modularFunctionFieldBar N` over $\overline{\mathbf Q}$ by the subgroup of principal divisors; it carries the natural action of $\mathrm{Gal}(\overline{\mathbf Q}/\mathbf Q)$, realised as $\overline{\mathbf Q}$-algebra automorphisms of $\overline{\mathbf Q}$ over $\mathbf Q$, and the module structure `heckeModuleBar N` over `HeckeAlg` $= \mathbf Z[X_p : p \text{ prime}]$, under which the variable at a prime $p$ acts by the operator `heckeOperatorBar N p` (this being the action when the operators `heckeOperatorBar N` commute pairwise). The assertion is that there exists a family of functions $B_k \colon J \times J \to \overline{\mathbf Q}$, indexed by $k \in \mathbf N$, such that for every $k$, restricted to the subgroup of $x$ with $\ell^k \cdot x = 0$: $B_k(x,y)^{\ell^k} = 1$; $B_k$ is additive-to-multiplicative in each of its two variables separately; $B_k$ has trivial left kernel and trivial right kernel, i.e. $B_k(x,y) = 1$ for all $\ell^k$-torsion $y$ forces $x = 0$, and symmetrically; $B_k(\sigma x, \sigma y) = \sigma(B_k(x,y))$ for every $\sigma \in \mathrm{Gal}(\overline{\mathbf Q}/\mathbf Q)$; $B_k(tx,y) = B_k(x,ty)$ for every $t \in$ `HeckeAlg`; and the two level-compatibilities $B_{k+1}(x,y) = B_k(\ell x, y)$ for $\ell^{k+1}$-torsion $x$ and $\ell^k$-torsion $y$, and $B_{k+1}(x,y) = B_k(x, \ell y)$ for $\ell^{k}$-torsion $x$ and $\ell^{k+1}$-torsion $y$.
--
--   This is the Weil pairing on the $\ell^k$-torsion of the Jacobian of $X_0(N)$, twisted so as to be Hecke-self-adjoint rather than Hecke-equivariant, produced as a family compatible under multiplication by $\ell$ so that it passes to the $\ell$-adic Tate module. It is used to construct a perfect, Galois-equivariant, Hecke-self-adjoint bilinear form on the Tate module, and in the computation of the determinant of Frobenius on residual Jacobian representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_pairing_family_pow_nsmul_eq_zero_galois_hecke_compat.lean

import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.exists_pairing_family_pow_nsmul_eq_zero_galois_hecke_compat
    (N : ℕ) [NeZero N] (ℓ : ℕ) (hℓ : ℓ ≠ 0) :
    letI := heckeModuleBar N
    ∃ B : ℕ → JZero N → JZero N → AlgebraicClosure ℚ,
      ∀ k : ℕ,
        (∀ x y : JZero N, ℓ ^ k • x = 0 → ℓ ^ k • y = 0 → B k x y ^ (ℓ ^ k) = 1) ∧
        (∀ x x' y : JZero N, ℓ ^ k • x = 0 → ℓ ^ k • x' = 0 → ℓ ^ k • y = 0 →
            B k (x + x') y = B k x y * B k x' y) ∧
        (∀ x y y' : JZero N, ℓ ^ k • x = 0 → ℓ ^ k • y = 0 → ℓ ^ k • y' = 0 →
            B k x (y + y') = B k x y * B k x y') ∧
        (∀ x : JZero N, ℓ ^ k • x = 0 → (∀ y : JZero N, ℓ ^ k • y = 0 → B k x y = 1) → x = 0) ∧
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x y : JZero N, ℓ ^ k • x = 0 → ℓ ^ k • y = 0 →
            B k (σ • x) (σ • y) = σ (B k x y)) ∧
        (∀ t : HeckeAlg, ∀ x y : JZero N, ℓ ^ k • x = 0 → ℓ ^ k • y = 0 → B k (t • x) y = B k x (t • y)) ∧
        (∀ y : JZero N, ℓ ^ k • y = 0 → (∀ x : JZero N, ℓ ^ k • x = 0 → B k x y = 1) → y = 0) ∧
        (∀ x y : JZero N, ℓ ^ (k + 1) • x = 0 → ℓ ^ k • y = 0 → B (k + 1) x y = B k (ℓ • x) y) ∧
        (∀ x y : JZero N, ℓ ^ k • x = 0 → ℓ ^ (k + 1) • y = 0 → B (k + 1) x y = B k x (ℓ • y)) := by sorry
