-- Prove2me | Theorems.Thm_ModularForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp
-- name    : ModularForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/c173ce8c-545f-5fc6-828d-f825a71f409e
-- title:
--   Basis of M_k(Γ₁(N)) with coefficients in ℚ(ζ_N)
-- statement:
--   Let $N$ be a natural number with $N \neq 0$ and let $k$ be an integer. The assertion is that there exist a natural number $n$ and a basis $b$ of the complex vector space $\mathrm{ModularForm}\,(\Gamma_1(N))\,k$ of modular forms of weight $k$ for the congruence subgroup $\Gamma_1(N)$, indexed by $\mathrm{Fin}\ n$ (so in particular the space is finite-dimensional over $\mathbb{C}$, with the basis given by an explicit finite index set), such that for every index $i$ and every natural number $m$ the quantity $\mathrm{qCoeff}\,(b\ i)\ m$ — by definition the coefficient of $q^m$ in the $q$-expansion of width $1$ of the function $b\ i$ on the upper half-plane, i.e. the $m$-th Fourier coefficient at the cusp $\infty$ in the variable $q = e^{2\pi i \tau}$ — lies in the intermediate field $\mathbb{Q}\bigl(e^{2\pi i/N}\bigr)$ of $\mathbb{C}/\mathbb{Q}$ obtained by adjoining to $\mathbb{Q}$ the single complex number $\exp(2\pi i/N)$, that is, in the $N$-th cyclotomic field inside $\mathbb{C}$. Both even and odd weights $k$, and all integers $k$ (including negative ones, where the space is zero), are covered.
--
--   This is the rationality statement that $M_k(\Gamma_1(N))$ is spanned over $\mathbb{C}$ by forms whose Fourier expansions at $\infty$ have coefficients in $\mathbb{Q}(\zeta_N)$, in the form used here for modular forms rather than cusp forms. It is the input to [`ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast`](thm.html#ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast), the descent to a basis with rational Fourier coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (ModularForm (CongruenceSubgroup.Gamma1 N) k)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈
        IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} := by sorry
