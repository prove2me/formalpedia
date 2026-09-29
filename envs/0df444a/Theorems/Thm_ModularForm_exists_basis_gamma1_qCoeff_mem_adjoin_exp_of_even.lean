-- Prove2me | Theorems.Thm_ModularForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even
-- name    : ModularForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/10239e92-d647-5dc2-a7d8-0ec29a4152f8
-- title:
--   Even-weight forms on Γ₁(N) have a ℚ(ζ_N)-rational basis
-- statement:
--   Let $N$ be a nonzero natural number and let $k$ be an even integer. The assertion is that there is a natural number $n$ and a $\mathbb{C}$-basis $b$, indexed by `Fin n`, of the space `ModularForm (CongruenceSubgroup.Gamma1 N) k` of modular forms of weight $k$ for $\Gamma_1(N)$ (the congruence subgroup of $\mathrm{SL}(2,\mathbb{Z})$, regarded as a subgroup of $\mathrm{GL}(2,\mathbb{R})$), with the following rationality property: for every index $i$ and every natural number $m$, the coefficient [`ModularFormClass.qCoeff (b i) m`](def/FLTPrelim_Modularity.html#L19), that is the $m$-th coefficient of the $q$-expansion of $b\,i$ taken with width $1$ (so the expansion in $q = e^{2\pi i \tau}$ at the cusp $\infty$), lies in the intermediate field $\mathbb{Q}\bigl(e^{2\pi i/N}\bigr)$ of $\mathbb{C}$ obtained by adjoining $\exp(2\pi i/N)$ to $\mathbb{Q}$. Thus the whole space, not merely its cuspidal part, admits a basis all of whose Fourier coefficients at $\infty$ are cyclotomic; no bound on $n$ or relation to the dimension is asserted, and nothing is claimed for odd $k$.
--
--   This is the rationality statement for even-weight modular forms on $\Gamma_1(N)$: the existence of a basis with Fourier coefficients in $\mathbb{Q}(\zeta_N)$, in the form used to descend $q$-expansions to the cyclotomic field. It feeds the corresponding statement for arbitrary weight, [`ModularForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp`](thm.html#ModularForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even (N : ℕ) [NeZero N] (k : ℤ)
    (hk : Even k) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (ModularForm (CongruenceSubgroup.Gamma1 N) k)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈
        IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} := by sorry
