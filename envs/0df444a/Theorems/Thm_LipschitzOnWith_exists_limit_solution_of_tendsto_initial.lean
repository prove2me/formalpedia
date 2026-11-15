-- Prove2me | Theorems.Thm_LipschitzOnWith_exists_limit_solution_of_tendsto_initial
-- name    : LipschitzOnWith.exists_limit_solution_of_tendsto_initial
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T20:31:15.384785+00:00
-- url     : https://prove2.me/theorems/613d987c-f32d-4615-a8aa-5c99bde8a54c
-- title:
--   Pointwise limits of solutions of a Lipschitz ODE with converging initial values
-- statement:
--   Let $E$ be a real Banach space, $S\subseteq E$ closed, and $R:E\to E$ Lipschitz on $S$ with constant $K$. Let $Q_k:\mathbb R\to E$ ($k\in\mathbb N$) satisfy $Q_k'(t)=R(Q_k(t))$ and $Q_k(t)\in S$ for all $t\in\mathbb R$. If $Q_k(0)\to p$, then there is $x:\mathbb R\to E$ with $x'(t)=R(x(t))$ and $x(t)\in S$ for all $t$, $x(0)=p$, and $Q_k(t)\to x(t)$ for every $t\in\mathbb R$.
--
--   This is the passage to the limit for complete solutions of a Lipschitz ODE confined to a closed invariant set, e.g. for sequences of periodic orbits of a flow on a compact energy surface.
--
--   Formalization Note: solutions are global, `∀ t, HasDerivAt (Q k) (R (Q k t)) t`; the Lipschitz hypothesis is `LipschitzOnWith K R S`, only on `S`.
-- source:
--   Standard (ODE theory)

import Mathlib

namespace LipschitzOnWith

open Filter Topology

/-- Let `R` be a vector field on a real Banach space `E` that is `K`-Lipschitz on a closed set
`S`, and let `Q k : ℝ → E` be solutions of `x' = R x` on all of `ℝ` that stay in `S`. If the
initial values `Q k 0` converge to `p`, then there is a solution `x : ℝ → E` of `x' = R x` with
values in `S` and `x 0 = p` such that `Q k t → x t` for every `t`. -/
theorem exists_limit_solution_of_tendsto_initial {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {R : E → E} {S : Set E} {K : NNReal}
    (hL : LipschitzOnWith K R S) (hS : IsClosed S)
    (Q : ℕ → ℝ → E) (hQ : ∀ k t, HasDerivAt (Q k) (R (Q k t)) t) (hQS : ∀ k t, Q k t ∈ S)
    (p : E) (h0 : Tendsto (fun k => Q k 0) atTop (𝓝 p)) :
    ∃ x : ℝ → E, (∀ t, HasDerivAt x (R (x t)) t) ∧ (∀ t, x t ∈ S) ∧ x 0 = p ∧
      ∀ t, Tendsto (fun k => Q k t) atTop (𝓝 (x t)) := by
  sorry

end LipschitzOnWith
