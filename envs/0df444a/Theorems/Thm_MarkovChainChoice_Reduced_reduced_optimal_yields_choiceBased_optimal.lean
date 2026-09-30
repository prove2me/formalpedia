-- Prove2me | Theorems.Thm_MarkovChainChoice_Reduced_reduced_optimal_yields_choiceBased_optimal
-- name    : MarkovChainChoice.Reduced.reduced_optimal_yields_choiceBased_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:35:39.017186+00:00
-- url     : https://prove2.me/theorems/f084e3d5-608d-44e7-ae70-97fca11ff5db
-- title:
--   Theorem 7 — an optimal (Reduced) solution decomposes into offer sets and yields an optimal (Choice Based) solution with the same value
-- statement:
--   Consider the network revenue management problem with $m$ resources of capacities $c_q$, a horizon of $T$ periods, revenues $r_j$ and resource consumptions $a_{q,j}$, where customers choose under a Markov chain choice model with $\lambda_j>0$, $\rho_{j,i}\ge0$ and $\sum_{i\in N}\rho_{j,i}<1$. Let $(\hat x,\hat z)$ be an optimal solution of the (Reduced) linear program. Then:
--
--   1. there exist subsets $S^1,\dots,S^K\subseteq N$ and positive scalars $\gamma^1,\dots,\gamma^K$ summing to one such that
--   $$\hat x = \sum_{k=1}^K\gamma^k P_{S^k}\qquad\text{and}\qquad \hat z = \sum_{k=1}^K\gamma^k R_{S^k};$$
--   2. for any such subsets and scalars, the solution $\hat u$ with $\hat u_{S^k}=\gamma^k$ for $k=1,\dots,K$ and $\hat u_S = 0$ for $S\notin\{S^1,\dots,S^K\}$ is optimal for the (Choice Based) linear program, and its objective value equals the objective value of $(\hat x,\hat z)$ in (Reduced); that is, the optimal objective values of the (Reduced) and (Choice Based) linear programs are the same.
--
--   The (Choice Based) program has $2^n$ variables while (Reduced) has $2n$ variables and $m+n$ constraints; the theorem says that solving the small program and decomposing its solution into offer sets solves the large one.
--
--   **Formalization Note** The optimal solution of (Reduced) is a hypothesis "feasible and at least as good as every feasible point". The vector $\hat u$ is `uHat S γ`, with $\hat u_S = \sum_{k:\,S^k=S}\gamma^k$: this is the paper's definition when the $S^k$ are distinct, and the only consistent reading when they are not. Part 2 is stated for every decomposition from part 1 (the paper's "In this case").
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1331, Theorem 7

import Mathlib
import Definitions.Def_MarkovChainChoice_Reduced_Model
import Definitions.Def_MarkovChainChoice_Reduced_LinearPrograms

namespace MarkovChainChoice.Reduced

theorem reduced_optimal_yields_choiceBased_optimal {m n : ℕ} (M : Model n) (T : ℕ)
    (a : Fin m → Fin n → ℝ) (c : Fin m → ℝ) (r : Fin n → ℝ) (x z : Fin n → ℝ)
    (hopt : IsReducedOptimal M T a c r (x, z)) :
    (∃ (K : ℕ) (S : Fin K → Finset (Fin n)) (γ : Fin K → ℝ),
        (∀ k, 0 < γ k) ∧ ∑ k, γ k = 1 ∧
        x = ∑ k, γ k • purchase M (S k) ∧ z = ∑ k, γ k • visitNot M (S k)) ∧
    ∀ (K : ℕ) (S : Fin K → Finset (Fin n)) (γ : Fin K → ℝ),
      (∀ k, 0 < γ k) → ∑ k, γ k = 1 →
      x = ∑ k, γ k • purchase M (S k) → z = ∑ k, γ k • visitNot M (S k) →
        IsChoiceBasedOptimal M T a c r (uHat S γ) ∧
          choiceBasedObjective M T r (uHat S γ) = reducedObjective T r (x, z) := by sorry

end MarkovChainChoice.Reduced
