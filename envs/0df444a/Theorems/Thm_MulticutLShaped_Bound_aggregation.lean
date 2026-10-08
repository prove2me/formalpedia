-- Prove2me | Theorems.Thm_MulticutLShaped_Bound_aggregation
-- name    : MulticutLShaped.Bound.aggregation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:15:25.342311+00:00
-- url     : https://prove2.me/theorems/06cfb7ba-11cf-4813-aa34-e1c0d95d9bfe
-- title:
--   Proof of the Proposition — aggregated multicut cuts give L-shaped cuts, and z(multi) ≥ z(L-shaped)
-- statement:
--   Fix feasibility cuts $F$, per-scenario optimality cuts $C_1,\dots,C_K$ and single L-shaped optimality cuts $L$. Suppose each cut $(E_l,e_l)$ of $L$ is an aggregate of one cut of each scenario: there are $(E_{l(k)},e_{l(k)})\in C_k$, $k=1,\dots,K$, with
--   $$E_l=\sum_{k=1}^K E_{l(k)},\qquad e_l=\sum_{k=1}^K e_{l(k)} .$$
--   Then
--   1. if $(x,\theta_1,\dots,\theta_K)$ is feasible in the multicut master (11)–(13), then $(x,\ \theta=\sum_{k=1}^K\theta_k)$ is feasible in the L-shaped master (4)–(6);
--   2. if $L$ is nonempty, $(x,\theta_1,\dots,\theta_K)$ is optimal for (11)–(13) and $(y,\eta)$ is optimal for (4)–(6), then
--   $$z(\text{multi}) = cx+\sum_{k=1}^K\theta_k\ \ge\ cy+\eta = z(\text{L-shaped}).$$
--
--   This is the comparison of the two master programs in the proof of the Proposition.
--
--   **Formalization Note** The paper compares the masters when "each constraint in (6) corresponds to K constraints in (13)"; part 2 assumes $L\ne\emptyset$, which forces every $C_k$ to be nonempty, so no $\theta_k$ is ignored. Without it, a scenario cut with negative right-hand side and no L-shaped cut would make the multicut value smaller. Optimal values are compared at attained optimal solutions.
-- source:
--   Birge and Louveaux, A multicut algorithm for two-stage stochastic linear programs, Eur. J. Oper. Res. 34 (1988), p. 387, Section 4, proof of the Proposition

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_MulticutLShaped_Bound_Masters

namespace MulticutLShaped.Bound

open StochasticProg.Recourse
open scoped Matrix

theorem aggregation {n1 n2 m1 m2 K : ℕ} (inst : Instance n1 n2 m1 m2 K)
    (F : List ((Fin n1 → ℝ) × ℝ)) (C : Fin K → List ((Fin n1 → ℝ) × ℝ))
    (L : List ((Fin n1 → ℝ) × ℝ))
    (hL : ∀ c ∈ L, ∃ sel : Fin K → (Fin n1 → ℝ) × ℝ, (∀ k, sel k ∈ C k) ∧
      c.1 = ∑ k, (sel k).1 ∧ c.2 = ∑ k, (sel k).2) :
    (∀ x θ, MultiFeasible inst F C x θ → LFeasible inst F L x (∑ k, θ k)) ∧
    (L ≠ [] → ∀ x θ y η, IsMultiOptimal inst F C x θ → IsLOptimal inst F L y η →
      LObj inst L y η ≤ multiObj inst C x θ) := by sorry

end MulticutLShaped.Bound
