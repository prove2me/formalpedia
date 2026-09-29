-- Prove2me | Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
-- name    : ModularCurve.charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/3477f93a-5b16-52ab-87af-126c16639d00
-- title:
--   Degeneracy roof at (N,q) equals full level-Nq function field
-- statement:
--   Let $k$ be a field carrying a `CharP k ℓ` instance for a natural number $\ell$ (primality of $\ell$ is not assumed), and let $N,q$ be natural numbers with $N\neq 0$, $q\neq 0$ and $Nq\neq 0$, subject to the single hypothesis $\ell\nmid Nq$. Inside the field $k((q))$ of Laurent series over $k$, write $\bar j =$ `jqModC k` for the Laurent series $q^{-1}$ times the reduction to $k$ of the integral power series `jNum`, and for $d\neq 0$ write $\bar j_d =$ `jqNModC k d`, the result of the substitution `qExpand k d` ($q\mapsto q^{d}$) applied to $\bar j$. The theorem asserts an equality of intermediate fields of $k((q))$ over $k$: the field `charLDegeneracyRoof k N q`, obtained by adjoining to $k$ the four elements $\bar j,\ \bar j_N,\ \bar j_q,\ \bar j_{Nq}$, coincides with `modularFunctionFieldFullC k (N*q)`, obtained by adjoining to $k$ the whole family of $q$-expansions $\bar j_d =$ `qExpand k d (jqModC k)` indexed by the nonzero divisors $d\mid Nq$.
--
--   The left-hand field is the common overfield of the two degeneracy maps $X_0(N)\leftarrow X_0(Nq)$ in characteristic $\ell$, and the statement identifies it with the full modular function field at level $Nq$, the carrier used for $J_0(Nq)$ over $k$; it is a characteristic-$\ell$ form of Igusa's two-generator description of the modular function field when the characteristic is prime to the level. It is invoked throughout the level-$Nq$ part of the development, for instance in the treatment of specialisations of modular curves and of Hecke correspondences.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul.lean

import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_CharLDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
set_option autoImplicit false

theorem ModularCurve.charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
    (k : Type*) [Field k]
    (ℓ : ℕ) [CharP k ℓ]
    (N : ℕ) [NeZero N] (q : ℕ) [NeZero q] [NeZero (N * q)]
    (hℓNq : ¬ ℓ ∣ N * q) :
    charLDegeneracyRoof k N q = modularFunctionFieldFullC k (N * q) := by sorry
