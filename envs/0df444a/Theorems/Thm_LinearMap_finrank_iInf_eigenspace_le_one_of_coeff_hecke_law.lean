-- Prove2me | Theorems.Thm_LinearMap_finrank_iInf_eigenspace_le_one_of_coeff_hecke_law
-- name    : LinearMap.finrank_iInf_eigenspace_le_one_of_coeff_hecke_law
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/974bcbf0-2b2c-5bcb-88cc-3de8a496fe65
-- title:
--   At most one dimension for a simultaneous Hecke eigenspace
-- statement:
--   Let $K$ be a field and $V$ a $K$-vector space. Suppose given a family of linear functionals $a_n \colon V \to K$ indexed by $n \in \mathbb{N}$ such that the functionals with $n \ge 1$ separate points, i.e. if $a_n(v) = 0$ for every $n \ge 1$ then $v = 0$; a family of $K$-linear endomorphisms $T_\ell \colon V \to V$ indexed by $\ell \in \mathbb{N}$; and scalars $c_\ell \in K$, subject to the coefficient law: for every prime $\ell$, every $n \ge 1$ and every $v \in V$, $$a_n(T_\ell v) = a_{n\ell}(v) + \bigl(\text{$c_\ell\, a_{n/\ell}(v)$ if $\ell \mid n$, and $0$ otherwise}\bigr),$$ where $n/\ell$ is natural-number division. Let $(\mu_n)_{n \in \mathbb{N}}$ be a further family of scalars and let $W = \bigcap_{\ell \text{ prime}} \ker(T_\ell - \mu_\ell)$, the infimum over primes $\ell$ of the $\mu_\ell$-eigenspaces of $T_\ell$. The conclusion is the conjunction of two assertions: first, any $v \in W$ with $a_1(v) = 0$ is zero; second, $\dim_K W \le 1$. Only the values $T_\ell$, $c_\ell$, $\mu_\ell$ at primes $\ell$ enter the hypotheses and the conclusion.
--
--   This is the algebraic content of the classical passage from a $q$-expansion principle to multiplicity one: a simultaneous Hecke eigenvector is determined by its first coefficient, so a simultaneous eigenspace on which the coefficient functionals separate points has dimension at most $1$. It is used in the analysis of Hecke eigenvectors on the Jacobian of a modular curve, in [`ModularCurve.eq_zero_or_exists_eq_nsmul_of_heckePic0Fibre_eq_eisenstein_of_heckeOperatorModL_eq_of_smul_eq_neg`](thm.html#ModularCurve.eq_zero_or_exists_eq_nsmul_of_heckePic0Fibre_eq_eisenstein_of_heckeOperatorModL_eq_of_smul_eq_neg).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_finrank_iInf_eigenspace_le_one_of_coeff_hecke_law.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LinearMap.finrank_iInf_eigenspace_le_one_of_coeff_hecke_law
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (a : ℕ → V →ₗ[K] K)
    (hinj : ∀ v : V, (∀ n : ℕ, 1 ≤ n → a n v = 0) → v = 0)
    (T : ℕ → V →ₗ[K] V) (c : ℕ → K)
    (hlaw : ∀ ℓ : ℕ, ℓ.Prime → ∀ n : ℕ, 1 ≤ n → ∀ v : V,
      a n (T ℓ v) = a (n * ℓ) v + (if ℓ ∣ n then c ℓ * a (n / ℓ) v else 0))
    (μ : ℕ → K) :
    (∀ v ∈ ⨅ (ℓ : ℕ) (_ : ℓ.Prime), Module.End.eigenspace (T ℓ) (μ ℓ), a 1 v = 0 → v = 0) ∧
    Module.finrank K ↥(⨅ (ℓ : ℕ) (_ : ℓ.Prime), Module.End.eigenspace (T ℓ) (μ ℓ)) ≤ 1 := by sorry
