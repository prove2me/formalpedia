-- Prove2me | Theorems.Thm_LinearMap_exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional
-- name    : LinearMap.exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/f29b4d88-7fc0-56ce-8564-9436d73bf810
-- title:
--   Pointwise limits of linear maps on a finite-dimensional function space are eventually injective
-- statement:
--   Let $X$ be a type and let $Y$ be a $\mathbb{C}$-submodule of the space $X \to \mathbb{C}$ of all complex-valued functions on $X$, assumed finite-dimensional over $\mathbb{C}$. Let $T \colon \mathbb{N} \to (Y \to_{\mathbb{C}} (X \to \mathbb{C}))$ be a sequence of $\mathbb{C}$-linear maps from $Y$ into the full function space, and suppose that for every $y \in Y$ and every $x \in X$ the sequence of complex numbers $(T_n y)(x)$ converges, along the filter `Filter.atTop` on $\mathbb{N}$, to the value $y(x)$ of the function $y$ at $x$. Then there exists an index $n$ such that $T_n$ has trivial kernel on $Y$: for every $y \in Y$, if $T_n y = 0$ (as a function on $X$) then $y = 0$. The conclusion asserts the existence of a single such index, not that the property holds for all large $n$, and injectivity is expressed as vanishing of the kernel rather than as `Function.Injective`.
--
--   This is the linear-algebra mechanism behind the statement that a sequence of operators converging pointwise to the identity on a finite-dimensional space of functions contains an injective member. It is used in the treatment of cuspidal constituents, where right convolution by members of an approximate identity is shown to be injective on a finite-dimensional space of automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LinearMap.exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional
    {X : Type*} (Y : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ ↥Y]
    (T : ℕ → (↥Y →ₗ[ℂ] (X → ℂ)))
    (hT : ∀ (y : ↥Y) (x : X), Filter.Tendsto (fun n => T n y x) Filter.atTop (nhds ((y : X → ℂ) x))) :
    ∃ n, ∀ y : ↥Y, T n y = 0 → y = 0 := by sorry
