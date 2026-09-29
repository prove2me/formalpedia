-- Prove2me | Theorems.Thm_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top
-- name    : IsAdicComplete.finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/037d384d-c71a-5f3e-8a27-552b60f20ba4
-- title:
--   Inverse limits of truncated modules over an adically complete ring
-- statement:
--   Let $R$ be a commutative ring and $I \subseteq R$ an ideal for which $R$ is $I$-adically complete (in Mathlib's sense, `IsAdicComplete I R`, i.e. Hausdorff and complete for the $I$-adic filtration). Let $M_n$, $n \in \mathbb{N}$, be $R$-modules and let $t_n : M_{n+1} \to M_n$ be $R$-linear maps, subject to three hypotheses for every $n$: $I^{n+1} \cdot M_n = 0$ (the top submodule of $M_n$ is annihilated by $I^{n+1}$), $t_n$ is surjective, and $\ker t_n \subseteq I^{n+1} \cdot M_{n+1}$; assume moreover that $M_0$ is a finite $R$-module. Finally let $L$ be a submodule of $\prod_n M_n$ whose members are exactly the compatible sequences, that is, $x \in L$ if and only if $t_n(x_{n+1}) = x_n$ for all $n$; so $L$ is the inverse limit $\varprojlim_n M_n$. The conclusion is threefold: $L$ is a finite $R$-module; for every $n$ and every $y \in M_n$ there is $x \in L$ with $x_n = y$, i.e. each projection $L \to M_n$ is surjective; and for every $n$ and every $x \in L$ one has $x_n = 0$ if and only if $x \in I^{n+1} \cdot L$. Together the last two assertions identify $L/I^{n+1}L$ with $M_n$.
--
--   This is the module-theoretic form of the standard statement that the inverse limit of a system of truncated modules over an $I$-adically complete ring is finitely generated and recovers each truncation, with no Noetherian hypothesis on $R$ and no finiteness hypothesis on $I$. It is used to produce a finite module over a complete ring from a compatible system of finite modules over the quotients $R/I^{n+1}$, as required for the deformation-theoretic constructions built on adic completions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem IsAdicComplete.finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top
    {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (t : ∀ n : ℕ, M (n + 1) →ₗ[R] M n)
    (hI : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (M n)) = ⊥)
    (ht : ∀ n : ℕ, Function.Surjective (t n))
    (hker : ∀ n : ℕ, LinearMap.ker (t n) ≤ I ^ (n + 1) • ⊤)
    [Module.Finite R (M 0)]
    (L : Submodule R (∀ n, M n)) (hL : ∀ x, x ∈ L ↔ ∀ n, t n (x (n + 1)) = x n) :
    Module.Finite R L ∧
      (∀ (n : ℕ) (y : M n), ∃ x ∈ L, x n = y) ∧
      (∀ (n : ℕ) (x : ∀ n, M n), x ∈ L → (x n = 0 ↔ x ∈ I ^ (n + 1) • L)) := by sorry
