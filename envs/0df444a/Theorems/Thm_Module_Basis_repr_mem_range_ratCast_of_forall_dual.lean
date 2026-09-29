-- Prove2me | Theorems.Thm_Module_Basis_repr_mem_range_ratCast_of_forall_dual
-- name    : Module.Basis.repr_mem_range_ratCast_of_forall_dual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/5115f2da-39ee-5cd0-aa23-601826d501cc
-- title:
--   Rational coordinates from a separating family of rational forms
-- statement:
--   Let $\iota$ be a finite index type, $V$ a complex vector space, and $b : \iota \to V$ a basis of $V$ over $\mathbb{C}$ indexed by $\iota$. Let $A$ be an arbitrary type and $\varphi : A \to (V \to_{\mathbb{C}} \mathbb{C})$ a family of $\mathbb{C}$-linear forms on $V$. Assume: (i) the family separates points, i.e. any $x \in V$ with $\varphi_a(x) = 0$ for all $a \in A$ is zero; (ii) the values of the family on the basis are rational, i.e. $\varphi_a(b_i)$ lies in the image of $\mathbb{Q} \to \mathbb{C}$ for every $a \in A$ and every $i \in \iota$. Let $h \in V$ be a vector such that $\varphi_a(h)$ lies in the image of $\mathbb{Q} \to \mathbb{C}$ for every $a \in A$, and let $i \in \iota$. Then the $i$-th coordinate $b.\mathrm{repr}\,h\,i$ of $h$ with respect to the basis $b$ also lies in the image of $\mathbb{Q} \to \mathbb{C}$, i.e. is a rational number. Rationality is expressed throughout as membership in `Set.range ((↑) : ℚ → ℂ)`.
--
--   This is the standard rationality criterion for coordinates: a vector whose values under a separating family of forms with rational values on a basis are rational has rational coordinates; equivalently, a linear system with rational coefficients and rational right-hand side that is solvable over $\mathbb{C}$ is solvable over $\mathbb{Q}$. It is used in the construction of a subalgebra with rational $q$-expansion coefficients attached to a weight-one Hecke eigenform, via [`DeligneSerre.exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen`](thm.html#DeligneSerre.exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Basis_repr_mem_range_ratCast_of_forall_dual.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Module.Basis.repr_mem_range_ratCast_of_forall_dual
    {ι : Type*} [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) {A : Type*} (φ : A → V →ₗ[ℂ] ℂ)
    (hinj : ∀ x : V, (∀ a : A, φ a x = 0) → x = 0)
    (hφb : ∀ (a : A) (i : ι), φ a (b i) ∈ Set.range ((↑) : ℚ → ℂ))
    (h : V) (hh : ∀ a : A, φ a h ∈ Set.range ((↑) : ℚ → ℂ)) (i : ι) :
    b.repr h i ∈ Set.range ((↑) : ℚ → ℂ) := by sorry
