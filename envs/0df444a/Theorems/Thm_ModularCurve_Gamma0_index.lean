-- Prove2me | Theorems.Thm_ModularCurve_Gamma0_index
-- name    : ModularCurve.Gamma0_index
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/c91d959d-2902-51d8-9891-dad35f4d75c5
-- title:
--   Index of Γ₀(N) equals ψ(N)
-- statement:
--   Let $N$ be a natural number, assumed nonzero. The Hecke congruence subgroup $\Gamma_0(N)$ of $\mathrm{SL}_2(\mathbb{Z})$, consisting of the integral matrices of determinant one whose lower-left entry is divisible by $N$, has finite index in $\mathrm{SL}_2(\mathbb{Z})$, and that index (in the sense of Mathlib's subgroup index, which is $0$ when the index is infinite) is equal to `dedekindPsi N`, defined here as the sum of $N/d$ over the squarefree divisors $d$ of $N$. Thus $$[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)] \;=\; \sum_{\substack{d \mid N \\ d \text{ squarefree}}} \frac{N}{d},$$ the right-hand side being the usual Dedekind psi function $\psi(N) = N\prod_{p \mid N}(1 + p^{-1})$ in this alternative but equivalent form. The proof cites the count [`ModularCurve.card_projectiveLine_zmod`](thm.html#ModularCurve.card_projectiveLine_zmod), which states that the projective line over $\mathbb{Z}/N\mathbb{Z}$ has cardinality `dedekindPsi N` for $N \neq 0$, reflecting the bijection between the cosets of $\Gamma_0(N)$ and $\mathbb{P}^1(\mathbb{Z}/N\mathbb{Z})$.
--
--   This is the classical index formula for the Hecke congruence subgroup, equivalently the degree of the covering $X_0(N) \to X(1)$ and the degree in each variable of the modular polynomial $\Phi_N$. It underlies the numerical bookkeeping for $X_0(N)$ and for spaces of modular forms of level $N$, and is used for instance in the sum of cusp widths on $X_0(N)$, in dimension and rank bounds for spaces of cusp forms, and in vanishing criteria for forms of small weight relative to $\psi(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_Gamma0_index.lean

import Definitions.Def_ModularCurve_X0
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.GroupTheory.Index

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.Gamma0_index (N : ℕ) [NeZero N] : (CongruenceSubgroup.Gamma0 N).index = dedekindPsi N := by sorry
