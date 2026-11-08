-- Prove2me | Theorems.Thm_NondualOpt_lemma_2
-- name    : NondualOpt.lemma_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-05T23:58:31.980414+00:00
-- url     : https://prove2.me/theorems/481ee076-0fa5-4616-9806-bcd24927021f
-- title:
--   Lemma 2 — max-regret online-to-batch
-- statement:
--   Let $X\subseteq E$ be convex and $U\subseteq X$, let $T\ge1$, let $x_1,\dots,x_T\in X$ be the queries of a max-regret game and let $f$ and $\ell_1,\dots,\ell_T$ be real functions with
--   $$
--   \ell_t(u)\le f(u)\ \ (u\in U),\qquad \ell_t(x_t)=f(x_t)\qquad(t\in[T]).
--   $$
--   Then the query $\hat x_T=x_{t_0}$ with the smallest value $f(x_{t_0})$ among $f(x_1),\dots,f(x_T)$ satisfies
--   $$
--   f(\hat x_T)-f(u)\le\frac{R^{\max}_{X,T}}{T}\qquad\text{for every }u\in U .
--   $$
--   In particular, if $f$ has a minimizer $x^*$ and $U=X$, one may take $u=x^*$. This reduces first-order optimization to the max-regret game: the linearizations $\ell_t(u)=f(x_t)+\langle g_t,u-x_t\rangle$ returned by the oracle satisfy both hypotheses.
--
--   Differences from the source:
--   - encoding: f : X → ℝ and ℓ_t : X → ℝ → functions on E; reason: only their values on X enter
--   - encoding: "we can compute x̂_T from (x_t)_{t∈[T]}" → x̂_T = x_{t₀} for some t₀ minimizing f(x_t), with the bound; reason: this is the proof's choice x̂_T ∈ arg min f(x_t), computed from the queries and their observed values
--   - encoding: f(x̂_T) − f(u) ≤ R^max_{X,T}/T → T·(f(x̂_T) − f(u)) ≤ R^max_{X,T} in the extended reals; reason: avoids extended-real division; equivalent for T ≥ 1
--   - encoding: rounds t ∈ [T] → T ≥ 1, rounds Fin T (0-based); reason: [T] is nonempty and the bound divides by T
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Lemma 2, p.8

import Mathlib
import Definitions.Def_NondualOpt_maxRegret

namespace NondualOpt

/-- **Lemma 2 (Max-regret online-to-batch).** For a convex set `X` and `U ⊆ X`, let `f` be a
function and `x_1, …, x_T ∈ X` queries of a max-regret game with losses `ℓ_t` satisfying
`ℓ_t(u) ≤ f(u)` for all `u ∈ U` and `ℓ_t(x_t) = f(x_t)`. Then the query `x̂_T = x_{t₀}` with the
smallest value `f(x_{t₀})` satisfies `f(x̂_T) − f(u) ≤ R^max_{X,T}/T` for every `u ∈ U`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Lemma 2, p.8.

**Formalization Note.** `x̂_T` is the arg-min query of the proof ("We use
`x̂_T ∈ arg min_{x_t} f(x_t)`"), computed from the queries and their observed values; the bound is
multiplied by `T` (no `EReal` division). `f` and `ℓ_t` are functions on `E`; only their values on
`X` enter. `T ≥ 1` (the rounds `[T]` are nonempty). -/
theorem lemma_2 {E : Type*} [AddCommGroup E] [Module ℝ E] (X U : Set E) (hX : Convex ℝ X)
    (hU : U ⊆ X) (T : ℕ) (hT : 1 ≤ T) (x : Fin T → E) (hx : ∀ t, x t ∈ X) (f : E → ℝ)
    (ℓ : Fin T → E → ℝ) (hℓU : ∀ t, ∀ u ∈ U, ℓ t u ≤ f u) (hℓx : ∀ t, ℓ t (x t) = f (x t)) :
    ∃ t₀ : Fin T, (∀ t, f (x t₀) ≤ f (x t)) ∧
      ∀ u ∈ U, (((T : ℝ) * (f (x t₀) - f u) : ℝ) : EReal) ≤ maxRegret X x ℓ := by sorry

end NondualOpt
