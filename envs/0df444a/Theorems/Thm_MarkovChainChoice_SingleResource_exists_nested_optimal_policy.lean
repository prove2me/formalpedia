-- Prove2me | Theorems.Thm_MarkovChainChoice_SingleResource_exists_nested_optimal_policy
-- name    : MarkovChainChoice.SingleResource.exists_nested_optimal_policy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:25:13.153985+00:00
-- url     : https://prove2.me/theorems/99ffee1b-1047-4867-baea-583d7dfdad35
-- title:
--   Theorem 5 — an optimal policy whose offer sets grow with remaining capacity and shrink with remaining time
-- statement:
--   Let $(\lambda,\rho)$ be a Markov chain choice model with the standing assumptions and $\sum_{j\in N}\lambda_j\le1$, let $r\in\mathbb R^n$ be the product revenues, $T$ the number of periods and $c$ the initial capacity. For $1\le t\le T$ and $1\le x\le c$, an optimal subset $\hat S_t(x)$ is an optimal solution of the problem on the right side of the (Single Resource) dynamic program,
--   $$\max_{S\subseteq N}\ \sum_{j\in N}P_{j,S}\{r_j+V_{t+1}(x-1)-V_{t+1}(x)\}.$$
--   Then there exists an optimal policy, that is, a choice of optimal subsets $\hat S_t(x)$ for all $1\le t\le T$ and $1\le x\le c$, such that
--   $$\hat S_t(x-1)\subseteq\hat S_t(x)\quad(1\le t\le T,\ 2\le x\le c)\qquad\text{and}\qquad \hat S_{t-1}(x)\subseteq\hat S_t(x)\quad(2\le t\le T,\ 1\le x\le c).$$
--
--   The first property says that the optimal offer set becomes smaller as remaining capacity decreases, so the optimal policy is a protection level policy: each product $j$ has a threshold $\bar x_{jt}$ and is offered in period $t$ exactly when the remaining capacity is at least $\bar x_{jt}$. The second says the optimal offer set becomes smaller when more periods remain.
--
--   **Formalization Note** The paper writes $\subset$ for non-strict inclusion. The first inclusion is stated for $x\ge2$: with zero units the dynamic program has no decision ($V_t(0)=0$ is a boundary condition), and the paper's later chain $\hat S_t(0)\subset\hat S_t(1)$ reads $\hat S_t(0)$ as $\emptyset$, for which the inclusion is trivial. The optimality clause is required of every $\hat S_t(x)$ in range, so the statement cannot be met by an arbitrary family of sets. One hypothesis is added, as in the marginal-value milestone: $\sum_j\lambda_j\le1$ (implied by the model of at most one arrival per period). No sign condition is placed on the revenues.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1329, Theorem 5

import Mathlib
import Definitions.Def_MarkovChainChoice_SingleResource_ValueFunction
open MarkovChainChoice.Shared

namespace MarkovChainChoice.SingleResource

theorem exists_nested_optimal_policy {n : ℕ} (M : Model n) (r : Fin n → ℝ) (T c : ℕ)
    (hlam : ∑ j, M.lam j ≤ 1) :
    ∃ Shat : ℕ → ℕ → Finset (Fin n),
      (∀ t x, 1 ≤ t → t ≤ T → 1 ≤ x → x ≤ c →
          ∀ S : Finset (Fin n), stageObj M r T t x S ≤ stageObj M r T t x (Shat t x)) ∧
        (∀ t x, 1 ≤ t → t ≤ T → 2 ≤ x → x ≤ c → Shat t (x - 1) ⊆ Shat t x) ∧
        ∀ t x, 2 ≤ t → t ≤ T → 1 ≤ x → x ≤ c → Shat (t - 1) x ⊆ Shat t x := by sorry

end MarkovChainChoice.SingleResource
