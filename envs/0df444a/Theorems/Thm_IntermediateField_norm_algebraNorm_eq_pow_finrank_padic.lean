-- Prove2me | Theorems.Thm_IntermediateField_norm_algebraNorm_eq_pow_finrank_padic
-- name    : IntermediateField.norm_algebraNorm_eq_pow_finrank_padic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/f891a54e-81ad-5cca-917f-496bd102db1a
-- title:
--   Norms scale the q-adic absolute value by the degree
-- statement:
--   Let $q$ be a prime number and let $\mathbb{Q}_q$ denote the field of $q$-adic numbers, with $\overline{\mathbb{Q}}_q =$ `PadicAlgCl q` an algebraic closure of it, carrying its canonical absolute value $\|\cdot\|$ (the spectral norm, so that $\|y\|$ is the spectral value of the minimal polynomial of $y$ over $\mathbb{Q}_q$). Let $K$ be an intermediate field of the extension $\mathbb{Q}_q \subseteq \overline{\mathbb{Q}}_q$ which is finite-dimensional over $\mathbb{Q}_q$, let $L$ be an intermediate field of $K \subseteq \overline{\mathbb{Q}}_q$ which is finite-dimensional over $K$, and let $w \in L$. Then the absolute value, computed in $\overline{\mathbb{Q}}_q$, of the image of the field norm $N_{L/K}(w) \in K$ equals $\|w\|^{[L:K]}$, where $w$ on the right-hand side is viewed in $\overline{\mathbb{Q}}_q$ and $[L:K]$ is the $K$-dimension of $L$. Both sides are computed after the canonical inclusions into $\overline{\mathbb{Q}}_q$, so no separate absolute value on $K$ or on $L$ is involved.
--
--   This is the standard multiplicativity of the $q$-adic absolute value under field norms, $\|N_{L/K}(w)\| = \|w\|^{[L:K]}$, for finite extensions inside a fixed algebraic closure of $\mathbb{Q}_q$. It is used in the local analysis of adjoining roots of unity to $q$-adic fields, in the construction of splittings of certain group-cohomology classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_norm_algebraNorm_eq_pow_finrank_padic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IntermediateField

theorem IntermediateField.norm_algebraNorm_eq_pow_finrank_padic (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (L : IntermediateField K (PadicAlgCl q)) [FiniteDimensional K L] (w : L) :
    ‖((Algebra.norm K w : K) : PadicAlgCl q)‖ = ‖(w : PadicAlgCl q)‖ ^ Module.finrank K L := by sorry
