-- Prove2me | Theorems.Thm_KallenbergLP_OptTransient_extreme_optimal_yields_pure_policy
-- name    : KallenbergLP.OptTransient.extreme_optimal_yields_pure_policy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:53:24.292556+00:00
-- url     : https://prove2.me/theorems/766bb23b-9629-4c60-9b84-a4c128de79c1
-- title:
--   Theorem 3.3.5 — an extreme LP optimum yields an optimal pure stationary policy
-- statement:
--   Consider a finite substochastic Markov decision model and positive weights $\beta_j>0$. Let $x^*$ be an extreme optimal solution of the equality-constrained program (3.3.7). Select, in each state $i$, an available action $f_*(i)$ for which $x^*_{i f_*(i)}>0$. Then the pure stationary policy $f_*^\infty$ is transient and optimal from every initial state among all transient policies:
--
--   $$
--   v_i(R)\le v_i(f_*^\infty)\qquad\text{for every transient policy }R\text{ and every }i\in E.
--   $$
--
--   The result turns an extreme LP optimum into a single pure policy that simultaneously maximizes all statewise transient values. The comparison class includes history-dependent randomized policies. No separate finiteness assumption on the value vector is made.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 57, Theorem 3.3.5; https://ir.cwi.nl/pub/13008

import Mathlib
import Definitions.Def_KallenbergLP_OptTransient_LinearProgram

namespace KallenbergLP.OptTransient

/-- Theorem 3.3.5, printed p. 57: an extreme LP optimum selects an optimal pure stationary policy. -/
theorem extreme_optimal_yields_pure_policy {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ)
    (hβ : ∀ i, 0 < β i)
    (x : StateAction m → ℝ)
    (hopt : IsOptimalLP m β x)
    (hext : x ∈ (feasibleSet m β).extremePoints ℝ)
    (f : (i : Fin n) → {a : α // a ∈ m.actions i})
    (hpositive : ∀ i, 0 < x ⟨i, f i⟩) :
    IsOptimalTransient m (purePolicy (fun i => (f i).1)) := by sorry

end KallenbergLP.OptTransient
