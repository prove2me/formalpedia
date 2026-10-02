-- Prove2me | Theorems.Thm_NonmonotoneSubmod_QueryLB_deterministic_average_bound
-- name    : NonmonotoneSubmod.QueryLB.deterministic_average_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:17:34.511384+00:00
-- url     : https://prove2.me/theorems/dcc79144-11b8-4296-b26f-46316956bf91
-- title:
--   §4.2 — deterministic algorithms with $q < e^{\epsilon^2 n/8}$ queries average at most $\tfrac14 n^2 + O(e^{-\epsilon^2 n/8})\,\mathrm{OPT}$
-- statement:
--   Let $n$ be even, $1 \le m$, $2m \le n$, $\epsilon = m/n$, and let $A$ be a deterministic adaptive algorithm making $q$ value queries with $q < e^{\epsilon^2 n/8}$. Averaging over all $C \subseteq [n]$ with $|C| = n/2$,
--
--   $$
--   \frac{1}{\binom{n}{n/2}} \sum_{|C| = n/2} f_C\bigl(A(f_C)\bigr) \le \frac{n^2}{4} + \Bigl(2e^{-\epsilon^2 n/8} + 2e^{-\epsilon^2 n/4}\Bigr)\Bigl(\frac{n^2}{2} - mn + m^2\Bigr).
--   $$
--
--   Here $\tfrac{n^2}{2} - mn + m^2$ is $\mathrm{OPT}(f_C)$, the same for every $C$. This is the deterministic case of the proof of Theorem 4.5: with probability close to $1$ over the random partition, all queries (and the returned set) are balanced, so the algorithm behaves as on the cut function $g$ and gains at most $\max g = \tfrac14 n^2$.
--
--   **Formalization Note** The average is written multiplied out, $\sum_C f_C(A(f_C)) \le \binom{n}{n/2}\cdot(\dots)$. The term $2e^{-\epsilon^2 n/8}$ is the paper's union bound over the queries; the extra $2e^{-\epsilon^2 n/4}$ accounts for the returned set, which must also be balanced for its value to be at most $\tfrac14 n^2$ (the paper counts only queries).
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1150, §4.2, proof of Theorem 4.5, first paragraph

import Mathlib
import Definitions.Def_NonmonotoneSubmod_QueryLB_HardInstance
import Definitions.Def_NonmonotoneSubmod_QueryLB_QueryAlgorithm

namespace NonmonotoneSubmod.QueryLB

/-- §4.2, proof of Theorem 4.5 (p. 1150, first paragraph), the deterministic case: for every
deterministic adaptive algorithm `A` with `q < e^{ϵ²n/8}` queries (`ϵ = m/n`), the average of
`f_C(A(f_C))` over the `n/2`-subsets `C` is at most
`n²/4 + (2e^{−ϵ²n/8} + 2e^{−ϵ²n/4})·(n²/2 − mn + m²)`. -/
theorem deterministic_average_bound (n m q : ℕ) (hn : Even n) (hm : 1 ≤ m) (hmn : 2 * m ≤ n)
    (hq : (q : ℝ) < Real.exp (((m : ℝ) / n) ^ 2 * n / 8)) (A : DetAlg (Fin n) q) :
    ∑ C ∈ Finset.univ.powersetCard (n / 2), fC n m C (A.run (fC n m C)) ≤
      (n.choose (n / 2) : ℝ) *
        ((n : ℝ) ^ 2 / 4 + (2 * Real.exp (-(((m : ℝ) / n) ^ 2 * n / 8)) +
          2 * Real.exp (-(((m : ℝ) / n) ^ 2 * n / 4))) *
          ((n : ℝ) ^ 2 / 2 - (m : ℝ) * n + (m : ℝ) ^ 2)) := by sorry

end NonmonotoneSubmod.QueryLB
