-- Prove2me | Theorems.Thm_ModularCurve_exists_pairing_nsmul_eq_zero_galois_hecke
-- name    : ModularCurve.exists_pairing_nsmul_eq_zero_galois_hecke
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/f9a202b0-ff8c-5cf7-a0b2-5e73c97fd35d
-- title:
--   A Fricke-twisted Weil pairing on J₀(N)[n]
-- statement:
--   Let $N$ be a nonzero natural number and let $n$ be a natural number with $n \neq 0$. Write $\overline{\mathbf Q}$ for `AlgebraicClosure ℚ` and let `JZero N` be the degree-zero divisor class group $\mathrm{Pic}^0$ of the function field `modularFunctionFieldBar N` (the base change to $\overline{\mathbf Q}$, inside Laurent series over $\overline{\mathbf Q}$, of the full modular function field of level $N$) over $\overline{\mathbf Q}$, i.e. degree-zero divisors modulo principal ones; it carries the natural action of the group of $\mathbf Q$-algebra automorphisms of $\overline{\mathbf Q}$, and, by the local instance `heckeModuleBar N`, a module structure over `HeckeAlg`, the polynomial ring $\mathbf Z[X_\ell : \ell \text{ prime}]$ in one variable per prime, acting through the Hecke operators `heckeOperatorBar N ℓ` (these commute, so the non-trivial branch of the definition applies). The assertion is that there exists a function $B \colon$ `JZero N` $\times$ `JZero N` $\to \overline{\mathbf Q}$, defined on all pairs but constrained only on $n$-torsion, such that for all $x,x',y,y'$ killed by $n$: $B(x,y)^n = 1$; $B(x+x',y) = B(x,y)B(x',y)$ and $B(x,y+y') = B(x,y)B(x,y')$; $B$ is nondegenerate in the first variable, i.e. if $B(x,y) = 1$ for every $n$-torsion $y$ then $x = 0$; $B(\sigma x, \sigma y) = \sigma(B(x,y))$ for every $\sigma \in \mathrm{Aut}_{\mathbf Q}(\overline{\mathbf Q})$; and $B(t x, y) = B(x, t y)$ for every $t \in$ `HeckeAlg`.
--
--   This is the Weil pairing on the $n$-torsion of the Jacobian of $X_0(N)$ twisted by the Fricke involution, which makes every Hecke operator self-adjoint while preserving bilinearity, $\mu_n$-valuedness, Galois equivariance and nondegeneracy; note that nondegeneracy is asserted only in the first variable. It is used to produce pairings on Hecke-stable subgroups of the torsion and, via Cartier duality, to compare the $n$-torsion with the dual of a model of it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_pairing_nsmul_eq_zero_galois_hecke.lean

import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.exists_pairing_nsmul_eq_zero_galois_hecke (N : ℕ) [NeZero N] (n : ℕ) (hn : n ≠ 0) :
    letI := heckeModuleBar N
    ∃ B : JZero N → JZero N → AlgebraicClosure ℚ,
      (∀ x y : JZero N, n • x = 0 → n • y = 0 → B x y ^ n = 1) ∧
      (∀ x x' y : JZero N, n • x = 0 → n • x' = 0 → n • y = 0 → B (x + x') y = B x y * B x' y) ∧
      (∀ x y y' : JZero N, n • x = 0 → n • y = 0 → n • y' = 0 → B x (y + y') = B x y * B x y') ∧
      (∀ x : JZero N, n • x = 0 → (∀ y : JZero N, n • y = 0 → B x y = 1) → x = 0) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x y : JZero N, n • x = 0 → n • y = 0 →
          B (σ • x) (σ • y) = σ (B x y)) ∧
      (∀ t : HeckeAlg, ∀ x y : JZero N, n • x = 0 → n • y = 0 → B (t • x) y = B x (t • y)) := by sorry
