-- Prove2me | Theorems.Thm_Module_End_exists_primitive_strings_basis_of_sl2_of_iSup_eigenspace_eq_top
-- name    : Module.End.exists_primitive_strings_basis_of_sl2_of_iSup_eigenspace_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/c5aee0bb-bbee-5897-824a-4938b4d49804
-- title:
--   Basis of mathfraksl₂-strings from primitive vectors
-- statement:
--   Let $V$ be a finite-dimensional complex vector space and let $e,f,h$ be $\mathbb{C}$-linear endomorphisms of $V$ satisfying the $\mathfrak{sl}_2$ commutation relations in the form $h\circ e-e\circ h=2e$, $h\circ f-f\circ h=-(2f)$ and $e\circ f-f\circ e=h$, and assume that the supremum of the eigenspaces $\ker(h-\mu)$ of $h$, taken over all $\mu\in\mathbb{C}$, is all of $V$. Then there exist a natural number $r$, vectors $t_0,\dots,t_{r-1}\in V$ and natural numbers $n_0,\dots,n_{r-1}$ such that: for each $i$ one has $e(t_i)=0$, $h(t_i)=n_i\,t_i$ and $f^{n_i+1}(t_i)=0$; for each $i$ and each $p\le n_i$ one has $h\bigl(f^p(t_i)\bigr)=(n_i-2p)\,f^p(t_i)$ and $e\bigl(f^{p+1}(t_i)\bigr)=(p+1)(n_i-p)\,f^p(t_i)$; and the family $(i,p)\mapsto f^{p}(t_i)$, indexed by the pairs with $0\le p\le n_i$, is linearly independent over $\mathbb{C}$ and spans $V$. The conclusion is thus given as an explicitly indexed independent spanning family rather than as a bundled basis.
--
--   This is complete reducibility for $\mathfrak{sl}_2(\mathbb{C})$ in elementary string form: a finite-dimensional module on which $h$ acts diagonalisably decomposes into strings $f^p t_i$ issuing from primitive (highest-weight) vectors, with the classical weight and lowering–raising formulas. It is used in the treatment of the archimedean component of automorphic forms, via [`AutomorphicForm.exists_su2Strings_of_finiteDimensional_of_isArchSmoothAtComplex`](thm.html#AutomorphicForm.exists_su2Strings_of_finiteDimensional_of_isArchSmoothAtComplex).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_End_exists_primitive_strings_basis_of_sl2_of_iSup_eigenspace_eq_top.lean

import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Module.End.exists_primitive_strings_basis_of_sl2_of_iSup_eigenspace_eq_top
    (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (e f h : V →ₗ[ℂ] V)
    (hhe : h ∘ₗ e - e ∘ₗ h = (2 : ℂ) • e) (hhf : h ∘ₗ f - f ∘ₗ h = -((2 : ℂ) • f)) (hef : e ∘ₗ f - f ∘ₗ e = h)
    (hdiag : ⨆ μ : ℂ, Module.End.eigenspace h μ = ⊤) :
    ∃ (r : ℕ) (t : Fin r → V) (n : Fin r → ℕ),
      (∀ i, e (t i) = 0 ∧ h (t i) = (n i : ℂ) • t i ∧ (f ^ (n i + 1)) (t i) = 0) ∧
      (∀ i (p : ℕ), p ≤ n i →
        h ((f ^ p) (t i)) = ((n i : ℂ) - 2 * (p : ℂ)) • (f ^ p) (t i) ∧
        e ((f ^ (p + 1)) (t i)) = (((p : ℂ) + 1) * ((n i : ℂ) - (p : ℂ))) • (f ^ p) (t i)) ∧
      LinearIndependent ℂ (fun x : (Σ i : Fin r, Fin (n i + 1)) => (f ^ (x.2 : ℕ)) (t x.1)) ∧
      Submodule.span ℂ (Set.range (fun x : (Σ i : Fin r, Fin (n i + 1)) => (f ^ (x.2 : ℕ)) (t x.1))) = ⊤ := by sorry
