-- Prove2me | Theorems.Thm_ModularForm_sturm_bound_Gamma0
-- name    : ModularForm.sturm_bound_Gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/5630553a-6fc0-536d-9a47-9de250f9e718
-- title:
--   Sturm bound for Γ₀(N) modular forms
-- statement:
--   Let $N$ be a nonzero natural number, let $k$ be an integer, and let $f$ be a modular form of weight $k$ for the congruence subgroup $\Gamma_0(N) \le \mathrm{SL}_2(\mathbb{Z})$, in Mathlib's sense (`ModularForm (CongruenceSubgroup.Gamma0 N) k`). Write $\mu =$ `(CongruenceSubgroup.Gamma0 N).index` for the index of $\Gamma_0(N)$ in $\mathrm{SL}_2(\mathbb{Z})$, and let the coefficients $a_n(f) =$ `(qExpansion 1 f).coeff n` be those of the $q$-expansion of $f$ of width $1$, i.e. in $q = e^{2\pi i \tau}$. The hypothesis is that $a_n(f) = 0$ for every natural number $n$ with $n \le \lfloor (k\mu)^{+}/12 \rfloor$, where $(k\mu)^{+}$ is the integer product $k \cdot \mu$ truncated to a natural number by `Int.toNat` (so the bound reads $0$ whenever $k\mu \le 0$) and the division is natural-number division. The conclusion is that $f = 0$ as a modular form. Note that the hypothesis is a vanishing condition on an explicit finite initial segment of the $q$-expansion, indexed inclusively by the Sturm bound.
--
--   This is Sturm's theorem for $\Gamma_0(N)$: vanishing of the Fourier coefficients of a weight-$k$ modular form up to $k[\mathrm{SL}_2(\mathbb{Z}):\Gamma_0(N)]/12$ forces the form to vanish, so forms of that weight and level are determined by finitely many coefficients. It is used downstream for cusp forms on $\Gamma_0(N)$: vanishing criteria in terms of the Dedekind $\psi$-function, finite generation of the lattice of integral cusp forms, and linear independence statements deduced from the behaviour of finitely many coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_sturm_bound_Gamma0.lean

import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularForm.sturm_bound_Gamma0 (N : ℕ) [NeZero N] {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (h : ∀ n : ℕ, n ≤ (k * (CongruenceSubgroup.Gamma0 N).index).toNat / 12 → (qExpansion 1 f).coeff n = 0) : f = 0 := by sorry
