-- Prove2me | Theorems.Thm_ModularForm_span_setOf_qCoeff_intCast_eq_top
-- name    : ModularForm.span_setOf_qCoeff_intCast_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/bcd6da70-53e3-5864-a18a-b4b2c4df092f
-- title:
--   Forms with integral q-expansion span M_k(Γ₀(N))
-- statement:
--   Let $N$ be a natural number, assumed nonzero, and let $k$ be an integer. Consider the complex vector space `ModularForm (CongruenceSubgroup.Gamma0 N) k` of modular forms of weight $k$ for the congruence subgroup $\Gamma_0(N) \le \mathrm{SL}_2(\mathbb{Z})$. For a function $f$ on the upper half-plane, [`ModularFormClass.qCoeff f n`](def/FLTPrelim_Modularity.html#L19) denotes the $n$-th coefficient of the $q$-expansion of $f$ of width $1$, i.e. the coefficient of $q^n$ in `qExpansion 1 f`. The theorem asserts that the $\mathbb{C}$-linear span of the set of those modular forms $f$ of weight $k$ on $\Gamma_0(N)$ such that for every natural number $n$ there is an integer $m$ with $\mathrm{qCoeff}(f)(n) = m$ in $\mathbb{C}$ — that is, all the $q$-expansion coefficients of $f$ at the cusp $\infty$ are rational integers — is the whole space $\top$. Equivalently, every modular form of weight $k$ on $\Gamma_0(N)$ is a finite $\mathbb{C}$-linear combination of modular forms with integral $q$-expansion; no cuspidality or positivity assumption on $k$ is imposed.
--
--   This is the statement that the lattice of forms with rational integral $q$-expansion coefficients generates the full space of modular forms over $\mathbb{C}$ (the integral structure on $M_k(\Gamma_0(N))$, classically obtained from the $q$-expansion principle or by Galois descent). It is used in the construction of mod $p$ modular forms and of eigensystems attached to them, in the step producing a mod $p$ eigenform from an eigensystem in the first cohomology of a binary form representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_span_setOf_qCoeff_intCast_eq_top.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularForm.span_setOf_qCoeff_intCast_eq_top (N : ℕ) [NeZero N] (k : ℤ) :
    Submodule.span ℂ {f : ModularForm (CongruenceSubgroup.Gamma0 N) k |
        ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff f n = (m : ℂ)} = ⊤ := by sorry
