-- Prove2me | Theorems.Thm_ManneLP_Equilibrium_lp_optimum_gives_optimal_rule
-- name    : ManneLP.Equilibrium.lp_optimum_gives_optimal_rule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:14:17.04066+00:00
-- url     : https://prove2.me/theorems/8124c91f-0e10-4bc3-8295-cc3adc7f8eab
-- title:
--   Assembled from §1, §3–§5, §7 (3) — an optimal solution of the equilibrium LP decodes to a stationary rule and equilibrium of least expected monthly cost
-- statement:
--   The paper states no labelled theorem; this statement assembles its claim from §1 (third paragraph), §3 (N.B.), §4 (last two paragraphs), §5 and §7 (3).
--
--   Consider Manne's inventory model: a positive integer bound $T$ on stock, admissible pairs $(i,j)$ with $i+j\le T$ and every $(i,0)$ admissible, a demand law $(p_n)$, and arbitrary real cost functions $C_1,C_2,C_3$ such that $\sum_np_nC_3(n-i-j)$ converges absolutely for every admissible pair. Consider the linear program
--   $$
--   \text{minimize}\ \sum_{i,j}c_{ij}x_{ij}\quad\text{subject to}\quad x_{ij}\ge0,\quad \sum_{i,j}x_{ij}=1,\quad \text{(8.1)–(8.T)},
--   $$
--   with $c_{ij}=C_1(i)+C_2(j)+\sum_np_nC_3(n-i-j)$ as in (10). Then:
--
--   1. the linear program has an optimal solution; and
--   2. for every optimal solution $x^*$, with $y^*_i=\sum_jx^*_{ij}$ and the decoded rule $q^*(j\mid i)=x^*_{ij}/y^*_i$ (produce nothing where $y^*_i=0$):
--      - $q^*$ is a stationary randomized decision rule and $y^*$ is a statistical equilibrium of $q^*$;
--      - the expected monthly cost (1) of $q^*$ in the equilibrium $y^*$ equals the optimal value $\sum_{i,j}c_{ij}x^*_{ij}$;
--      - this cost is at most the expected monthly cost (1) of **every** stationary randomized rule $q$ in **every** statistical equilibrium $y$ of $q$.
--
--   This is the paper's main point: the requirements of statistical equilibrium furnish linear constraints, the expected cost under the equilibrium probabilities is a linear objective, and the simplex method therefore finds an optimal sequential decision rule.
--
--   **Formalization Note** The comparison ranges over all pairs (rule, equilibrium) because the chain of a rule need not be irreducible (§7 (3): when it is "decomposable" the initial conditions govern the equilibrium, and the decision-maker is assumed to choose them); no irreducibility, aperiodicity or uniqueness of equilibria is assumed, and mixed rules are allowed. The expected monthly cost is defined from the joint law of initial stock, production and demand, not as $\sum c_{ij}x_{ij}$. The absolute-summability hypothesis on the shortage cost is not on the page, which takes the expectation for granted. At stock levels with $y^*_i=0$ the page's quotient is $0/0$; the default action there is a choice of the formalization.
-- source:
--   Manne, Linear Programming and Sequential Decisions, Management Science 6 (1960), assembled from p. 259 (§1, third paragraph), p. 261 (§3, N.B.), p. 262 (§4, last two paragraphs; §5, (9), (10)), p. 264 (§7 (3))

import Mathlib
import Definitions.Def_ManneLP_Equilibrium_Model
import Definitions.Def_ManneLP_Equilibrium_Chain
import Definitions.Def_ManneLP_Equilibrium_LP

namespace ManneLP.Equilibrium

theorem lp_optimum_gives_optimal_rule (M : Model)
    (hsum : ∀ a ∈ M.A,
      Summable (fun n : ℕ => M.p n * M.C₃ ((n : ℤ) - (a.1 : ℤ) - (a.2 : ℤ)))) :
    (∃ x : ℕ × ℕ → ℝ, IsLPOptimal M x) ∧
    ∀ x : ℕ × ℕ → ℝ, IsLPOptimal M x →
      IsRule M (decodeRule M x) ∧
      IsEquilibrium M (decodeRule M x) (decodeDist M x) ∧
      eqCost M (decodeRule M x) (decodeDist M x) = lpObj M x ∧
      ∀ (q : ℕ → ℕ → ℝ) (y : ℕ → ℝ), IsRule M q → IsEquilibrium M q y →
        eqCost M (decodeRule M x) (decodeDist M x) ≤ eqCost M q y := by sorry

end ManneLP.Equilibrium
