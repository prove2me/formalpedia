-- Prove2me | Theorems.Thm_ModularForm_exists_basis_gamma1_qCoeff_mem_range_ratCast
-- name    : ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/d8bc0691-741b-5ee2-a41c-74a968a18edb
-- title:
--   Rational basis for M_k(Γ₁(N))
-- statement:
--   Let $N$ be a natural number, assumed nonzero, and let $k$ be an integer. The assertion is that there exist a natural number $n$ and a basis $b$ of the complex vector space $\mathrm{ModularForm}(\Gamma_1(N), k)$ of weight-$k$ modular forms for the congruence subgroup $\Gamma_1(N)$, indexed by `Fin n`, such that for every index $i$ and every natural number $m$ the $m$-th coefficient [`ModularFormClass.qCoeff (b i) m`](def/FLTPrelim_Modularity.html#L19) lies in the image of the coercion $\mathbb{Q} \to \mathbb{C}$, i.e. is a rational number. Here `qCoeff f m` is by definition the $m$-th coefficient of the $q$-expansion of $f : \mathbb{H} \to \mathbb{C}$ taken with width $1$, that is the coefficient of $q^m$ in the expansion of $f$ in $q = e^{2\pi i \tau}$. In particular the space is asserted to be finite-dimensional, the dimension being the $n$ produced; no holomorphy or growth condition beyond those built into the type `ModularForm` is imposed, and no normalisation of the basis beyond rationality of all its $q$-expansion coefficients is claimed.
--
--   This is the rational structure of the space of modular forms of weight $k$ and level $\Gamma_1(N)$: $M_k(\Gamma_1(N))$ has a basis whose Fourier expansions at $\infty$ have rational coefficients. It is obtained from the corresponding statement with coefficients in $\mathbb{Q}(e^{2\pi i/N})$ together with the stability of the space under Galois conjugation of $q$-expansion coefficients, and is used in the construction of models over $\mathbb{Q}$ via [`ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1`](thm.html#ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_basis_gamma1_qCoeff_mem_range_ratCast.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (ModularForm (CongruenceSubgroup.Gamma1 N) k)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈ Set.range ((↑) : ℚ → ℂ) := by sorry
