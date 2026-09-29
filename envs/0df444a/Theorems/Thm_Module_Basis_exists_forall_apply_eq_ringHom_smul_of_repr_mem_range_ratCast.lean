-- Prove2me | Theorems.Thm_Module_Basis_exists_forall_apply_eq_ringHom_smul_of_repr_mem_range_ratCast
-- name    : Module.Basis.exists_forall_apply_eq_ringHom_smul_of_repr_mem_range_ratCast
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/18589b7f-31a4-5e2a-9fbe-7b1a505eb9cb
-- title:
--   Galois conjugation of a common eigenvector of rational operators
-- statement:
--   Let $\iota$ be a finite index type and $V$ a complex vector space equipped with a basis $b=(b_i)_{i\in\iota}$ indexed by $\iota$. Let $J$ be an arbitrary index type and $(S_j)_{j\in J}$ a family of $\mathbb{C}$-linear endomorphisms of $V$ whose matrix entries in this basis are rational, i.e. for all $j\in J$ and $i,i'\in\iota$ the coordinate $b.\mathrm{repr}(S_j b_i)(i')$ lies in the image of $\mathbb{Q}\to\mathbb{C}$; let $\ell\colon V\to\mathbb{C}$ be a $\mathbb{C}$-linear form with $\ell(b_i)$ in the image of $\mathbb{Q}\to\mathbb{C}$ for every $i$. Let $\lambda\colon J\to\mathbb{C}$ and let $v\in V$ satisfy $S_j v=\lambda_j v$ for all $j$, together with $\ell(v)\neq 0$. Finally let $R$ be a $\mathbb{Z}$-subalgebra of $\mathbb{C}$ that is finite as a $\mathbb{Z}$-module, assume $\lambda_j\in R$ for every $j$, and let $\tau\colon R\to\mathbb{C}$ be a ring homomorphism. Then there exists $w\in V$ with $\ell(w)\neq 0$ and $S_j w=\tau(\lambda_j)\,w$ for all $j\in J$, where $\lambda_j$ is regarded as the element $\langle\lambda_j,\ hR\,j\rangle$ of $R$.
--
--   This is the linear algebra underlying the fact that Galois conjugates of Hecke eigenforms are again Hecke eigenforms with conjugated eigenvalues (Deligne–Serre (2.7.4); Shimura, §3.5), phrased for an abstract family of commuting-free operators with rational matrices and a rational-valued linear form used as a nonvanishing test functional (typically a Fourier coefficient). It is invoked in the weight one Deligne–Serre argument, in the construction of a subalgebra containing the eigenvalues all of whose embeddings into $\mathbb{C}$ are realised by eigenvectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Basis_exists_forall_apply_eq_ringHom_smul_of_repr_mem_range_ratCast.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Module.Basis.exists_forall_apply_eq_ringHom_smul_of_repr_mem_range_ratCast
    {ι : Type*} [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) {J : Type*} (S : J → V →ₗ[ℂ] V)
    (hS : ∀ (j : J) (i i' : ι), b.repr (S j (b i)) i' ∈ Set.range ((↑) : ℚ → ℂ))
    (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ∀ i : ι, ℓ (b i) ∈ Set.range ((↑) : ℚ → ℂ))
    (lam : J → ℂ) (v : V) (hv : ∀ j : J, S j v = lam j • v) (hℓv : ℓ v ≠ 0)
    (R : Subalgebra ℤ ℂ) [Module.Finite ℤ R] (hR : ∀ j : J, lam j ∈ R) (τ : R →+* ℂ) :
    ∃ w : V, ℓ w ≠ 0 ∧ ∀ j : J, S j w = τ ⟨lam j, hR j⟩ • w := by sorry
