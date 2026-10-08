-- Prove2me | Theorems.Thm_LovejoyPOMDP_Monotone_proposition_1_infinite
-- name    : LovejoyPOMDP.Monotone.proposition_1_infinite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:57:14.65782+00:00
-- url     : https://prove2.me/theorems/ab1b0e69-6303-4867-8686-0d6e6e177678
-- title:
--   Proposition 1, part 2 — the infinite-horizon V* is nondecreasing on (Π(S), ≥r)
-- statement:
--   Consider a finite POMDP as in §2 of the paper with infinite horizon and discount factor $0<\beta<1$. Assume (b)–(d) of Proposition 1, part 1:
--
--   1. (b) $g(\cdot,a)$ is nondecreasing on $S$ for each $a\in A$;
--   2. (c) $P^a$ is $\mathrm{TP}_2$ for each $a\in A$;
--   3. (d) $r^a(j)\ge_r r^a(j')$ for $j\ge j'$ in $S$ and $a\in A$.
--
--   Let $V^*$ be the infinite-horizon optimal value function, i.e. the bounded solution on $\Pi(S)$ of
--   $$V^*(\pi)=\max_{a\in A} h(\pi,a,V^*).$$
--   Then $\pi\ge_r\pi'$ in $\Pi(S)$ implies $V^*(\pi)\ge V^*(\pi')$.
--
--   **Formalization Note** $V^*$ is any `V` with `M.IsBellmanSolution V` (bounded on $\Pi(S)$ and solving the Bellman equation there). For $0<\beta<1$ such a $V$ exists and is unique on $\Pi(S)$, because the Bellman operator is a $\beta$-contraction in the sup-metric $\rho$ of p. 738. The hypothesis is therefore satisfiable and singles out the paper's $V^*$.
-- source:
--   Lovejoy, Some Monotonicity Results for Partially Observed Markov Decision Processes, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, p. 739, Proposition 1, part 2

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Model

namespace LovejoyPOMDP.Monotone

/-- Lovejoy, *Some Monotonicity Results for Partially Observed Markov Decision Processes*, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, p. 739, Proposition 1, part 2 (`N = ∞`).

Let `0 < β < 1`. Under assumptions (b)–(d) of part 1, `π ≥r π'` in `Π(S)` implies
`V*(π) ≥ V*(π')`, where `V*` is the infinite-horizon optimal value function.

**Formalization Note.** `V*` is represented as any `V` that is bounded on `Π(S)` and satisfies
`V(π) = max_a h(π, a, V)` on `Π(S)` (`POMDP.IsBellmanSolution`). For `0 < β < 1` this solution
exists and is unique on `Π(S)` (contraction in the sup-metric `ρ`, p. 738); it is the limit `V*`
of the recursion (3). -/
theorem proposition_1_infinite {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]
    [LinearOrder S] [LinearOrder O] [LinearOrder A] [Nonempty S] [Nonempty O] [Nonempty A]
    (M : POMDP S O A)
    (hβ₀ : 0 < M.β) (hβ₁ : M.β < 1)
    (hg : ∀ a, Monotone (fun i => M.g i a))
    (hP : ∀ a, TP2 (M.P a))
    (hR : ∀ a (j j' : S), j' ≤ j → MLRGE (M.R a j) (M.R a j'))
    (V : (S → ℝ) → ℝ) (hV : M.IsBellmanSolution V)
    {π π' : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) (hπ' : π' ∈ stdSimplex ℝ S) (h : MLRGE π π') :
    V π' ≤ V π := by sorry

end LovejoyPOMDP.Monotone
