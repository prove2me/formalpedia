-- Prove2me | Theorems.Thm_LevelRaising_exists_mem_range_of_forall_exists_add_dvd
-- name    : LevelRaising.exists_mem_range_of_forall_exists_add_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/0c2e21ab-4994-56b8-9423-795583a00e70
-- title:
--   Unit-local surjectivity from surjectivity modulo p
-- statement:
--   Let $C_1$ and $C_0$ be additive commutative groups, regarded as $\mathbb{Z}$-modules, with $C_0$ finitely generated over $\mathbb{Z}$; let $\tau_1 : C_1 \to C_1$ and $\tau_0 : C_0 \to C_0$ be $\mathbb{Z}$-linear endomorphisms and $\beta : C_1 \to C_0$ a $\mathbb{Z}$-linear map intertwining them, in the sense that the composite $\tau_1$ followed by $\beta$ equals the composite $\beta$ followed by $\tau_0$. Let $p$ be a natural number assumed prime and $a \in \mathbb{Z}$. The hypothesis is that for every $h \in C_0$ there exist an integer polynomial $s$ with $s(a) \not\equiv 0 \pmod p$, an element $x \in C_1$ and an element $h' \in C_0$ such that $s(\tau_0)\,h = \beta x + p\,h'$, where $s(\tau_0)$ denotes the evaluation of $s$ at $\tau_0$ in the endomorphism algebra. The conclusion is that for every $h \in C_0$ there exist an integer polynomial $s$ with $s(a) \not\equiv 0 \pmod p$ and an element $x \in C_1$ with $s(\tau_0)\,h = \beta x$ exactly; that is, the error term divisible by $p$ can be removed at the cost of changing the polynomial $s$, which remains a unit at $(a,p)$.
--
--   This is Nakayama's lemma applied to the cokernel of $\beta$, phrased in the language of a finitely generated $\mathbb{Z}$-module with one operator $\tau_0$ and localisation at the maximal ideal $(p, X-a)$ of $\mathbb{Z}[X]$: surjectivity of $\beta$ after reduction modulo $p$ in this local sense implies surjectivity itself. It is used in the level-raising part of the argument, in the analysis of the support of the $q$-new part attached to a normalised eigenform at an odd prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LevelRaising_exists_mem_range_of_forall_exists_add_dvd.lean

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Field.ZMod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LevelRaising.exists_mem_range_of_forall_exists_add_dvd
    {C₁ C₀ : Type*} [AddCommGroup C₁] [AddCommGroup C₀] [Module.Finite ℤ C₀]
    (τ₁ : C₁ →ₗ[ℤ] C₁) (τ₀ : C₀ →ₗ[ℤ] C₀) (β : C₁ →ₗ[ℤ] C₀)
    (hβτ : β ∘ₗ τ₁ = τ₀ ∘ₗ β)
    {p : ℕ} [Fact p.Prime] (a : ℤ)
    (hyp : ∀ h : C₀, ∃ s : Polynomial ℤ, ((s.eval a : ℤ) : ZMod p) ≠ 0 ∧
      ∃ x : C₁, ∃ h' : C₀, (Polynomial.aeval τ₀ s) h = β x + (p : ℤ) • h') :
    ∀ h : C₀, ∃ s : Polynomial ℤ, ((s.eval a : ℤ) : ZMod p) ≠ 0 ∧
      ∃ x : C₁, (Polynomial.aeval τ₀ s) h = β x := by sorry
