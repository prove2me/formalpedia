-- Prove2me | Theorems.Thm_NonmonotoneSubmod_QueryLB_query_lower_bound
-- name    : NonmonotoneSubmod.QueryLB.query_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:18:06.793418+00:00
-- url     : https://prove2.me/theorems/b47ac9e1-f74a-47c6-8a18-57207a643cca
-- title:
--   Theorem 4.5 — beating $1/2$ for symmetric submodular maximization needs $e^{\epsilon^2 n/8}$ value queries
-- statement:
--   Let $n$ be even and $m$ an integer with $1 \le m$ and $2m \le n$; put $\epsilon = m/n \in (0, \tfrac12]$. For $C \subseteq [n]$ with $|C| = n/2$ let $f_C$ be the hard instance of the paper's construction. Then:
--
--   1. **The instances.** For every such $C$, $f_C$ is nonnegative, symmetric ($f_C([n]\setminus S) = f_C(S)$) and submodular, and
--   $$
--   \mathrm{OPT}(f_C) = \frac{n^2}{2} - mn + m^2 = \tfrac12 n^2(1 - 2\epsilon + 2\epsilon^2).
--   $$
--   2. **The lower bound.** For every number of queries $q < e^{\epsilon^2 n/8}$ and every randomized adaptive algorithm $\mu$ making $q$ value queries, there is a $C$ with $|C| = n/2$ such that
--   $$
--   \mathbb{E}_{A\sim\mu}\bigl[f_C(A(f_C))\bigr] \le \frac{n^2}{4} + \Bigl(2e^{-\epsilon^2 n/8} + 2e^{-\epsilon^2 n/4}\Bigr)\,\mathrm{OPT}(f_C).
--   $$
--
--   Dividing by $\mathrm{OPT}(f_C)$, the expected value is at most $\bigl(\frac{1}{2(1-2\epsilon+2\epsilon^2)} + 4e^{-\epsilon^2 n/8}\bigr)\mathrm{OPT}$. Since $\frac{1}{2(1-2\epsilon+2\epsilon^2)} = \frac12 + \epsilon + O(\epsilon^2)$, for every fixed $\epsilon > 0$ and $n \to \infty$ no algorithm with fewer than $e^{\epsilon^2 n/8}$ queries achieves a ratio better than $\tfrac12 + O(\epsilon)$ on symmetric nonnegative submodular functions. The factor $\tfrac12$ is achieved by the random set for symmetric functions, so it is optimal in the value-oracle model.
--
--   **Formalization Note** This is the explicit form of the printed statement ("fewer than $e^{\epsilon^2 n/8}$ queries", "expected value at least $(\tfrac12 + \epsilon)\mathrm{OPT}$"), pinned down to what the proof establishes. On the proof's instances with the same $\epsilon$, the achievable ratio is $\frac{1}{2(1-2\epsilon+2\epsilon^2)}$, which exceeds $\tfrac12 + \epsilon$; the printed pair holds only after reparametrizing $\epsilon$. The error term $2e^{-\epsilon^2n/4}$ for the returned set is added (the paper counts only queries). A randomized algorithm is a `PMF` over deterministic $q$-query algorithms (countable support), and its expected value is the finite sum over output sets. The instance may depend on the algorithm (for every algorithm there is a hard instance), and $C$ ranges over exactly the paper's family. $\epsilon n$ is the integer $m$, as the paper assumes.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1149, Theorem 4.5, with its proof pp. 1149–1150

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_SymmetricSetFun
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_QueryLB_HardInstance
import Definitions.Def_NonmonotoneSubmod_QueryLB_QueryAlgorithm

namespace NonmonotoneSubmod.QueryLB

/-- Theorem 4.5 (Feige–Mirrokni–Vondrák 2011, p. 1149), with the constants its proof delivers.
For `n` even and `ϵ = m/n` with `1 ≤ m`, `2m ≤ n`:
1. every `f_C` (`|C| = n/2`) is nonnegative, symmetric and submodular, with
   `OPT(f_C) = n²/2 − mn + m²`;
2. for every randomized adaptive algorithm with `q < e^{ϵ²n/8}` value queries (a distribution
   `μ` over deterministic `q`-query algorithms) there is a balanced `C` on which its expected
   value is at most `n²/4 + (2e^{−ϵ²n/8} + 2e^{−ϵ²n/4})·OPT(f_C)`. -/
theorem query_lower_bound (n m : ℕ) (hn : Even n) (hm : 1 ≤ m) (hmn : 2 * m ≤ n) :
    (∀ C : Finset (Fin n), C.card = n / 2 →
      (∀ S, 0 ≤ fC n m C S) ∧ NonmonotoneSubmod.Shared.SymmetricSetFun (fC n m C) ∧ NonmonotoneSubmod.Shared.Submodular (fC n m C) ∧
        NonmonotoneSubmod.Shared.OPT (fC n m C) = (n : ℝ) ^ 2 / 2 - (m : ℝ) * n + (m : ℝ) ^ 2) ∧
    ∀ q : ℕ, (q : ℝ) < Real.exp (((m : ℝ) / n) ^ 2 * n / 8) →
      ∀ μ : PMF (DetAlg (Fin n) q), ∃ C : Finset (Fin n), C.card = n / 2 ∧
        expectedValue μ (fC n m C) ≤
          (n : ℝ) ^ 2 / 4 + (2 * Real.exp (-(((m : ℝ) / n) ^ 2 * n / 8)) +
            2 * Real.exp (-(((m : ℝ) / n) ^ 2 * n / 4))) * NonmonotoneSubmod.Shared.OPT (fC n m C) := by sorry

end NonmonotoneSubmod.QueryLB
