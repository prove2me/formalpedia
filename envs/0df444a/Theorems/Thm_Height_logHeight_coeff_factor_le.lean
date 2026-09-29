-- Prove2me | Theorems.Thm_Height_logHeight_coeff_factor_le
-- name    : Height.logHeight_coeff_factor_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/d4658681-588b-5bbc-98fa-b8e9f6392a32
-- title:
--   Coefficient-height bound for monic factors over a number field
-- statement:
--   Let $K$ be a number field and let $n$ be a natural number. The assertion is the existence of a real constant $c$ — depending only on $K$ and $n$, since it is quantified before $p$ and $q$ — such that for all polynomials $p, q \in K[X]$ satisfying $p \neq 0$, $\deg p \le n$ (as `natDegree`), $q$ monic and $q \mid p$, one has
--   $$\mathrm{logHeight}\bigl((q_k)_{k \in \{0,\dots,n\}}\bigr) \le \mathrm{logHeight}\bigl((p_k)_{k \in \{0,\dots,n\}}\bigr) + c,$$
--   where $p_k$ and $q_k$ denote the $k$-th coefficients and $\mathrm{logHeight}$ is the logarithmic height `Height.logHeight` of a finite family of elements of $K$. Both families are indexed by `Fin (n + 1)`, i.e. the coefficient vectors are truncated after degree $n$; the degree hypothesis on $p$, together with monicity of $q$ and $q \mid p$, ensures that all coefficients of $p$ and of $q$ occur among those listed. The hypothesis $p \neq 0$ cannot be dropped, since every monic polynomial divides $0$ while the zero coefficient vector has height $0$.
--
--   This is the standard Mignotte–Landau-type estimate bounding the height of the coefficients of a monic factor in terms of the height of the coefficients of a multiple, uniformly over factorisations of polynomials of bounded degree; Gauss's lemma makes the finite places exact, so only the archimedean places contribute to $c$. It is used in the construction of height systems on modular curves, being cited by [`ModularCurve.JZero.naiveHeight_reduce`](thm.html#ModularCurve.JZero.naiveHeight_reduce) and [`ModularCurve.exists_height_system_modularFunctionFieldBar`](thm.html#ModularCurve.exists_height_system_modularFunctionFieldBar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Height_logHeight_coeff_factor_le.lean

import Mathlib.NumberTheory.Height.NumberField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Height.logHeight_coeff_factor_le (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    ∃ c : ℝ, ∀ p q : Polynomial K, p ≠ 0 → p.natDegree ≤ n → q.Monic → q ∣ p →
      Height.logHeight (fun k : Fin (n + 1) => q.coeff k)
        ≤ Height.logHeight (fun k : Fin (n + 1) => p.coeff k) + c := by sorry
