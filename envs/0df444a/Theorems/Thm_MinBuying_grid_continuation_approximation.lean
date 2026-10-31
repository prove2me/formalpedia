-- Prove2me | Theorems.Thm_MinBuying_grid_continuation_approximation
-- name    : MinBuying.grid_continuation_approximation
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T17:26:38.409252+00:00
-- url     : https://prove2.me/theorems/96353caf-3867-41fe-9643-2dc41168b4d4
-- title:
--   Finite-grid approximation of the benchmark continuation
-- statement:
--   Fix $0\le u<v<1$ and the paper's functions $A,c$. For every $\varepsilon>0$ there is a positive integer $m$ such that, on the grid $x_k=u+(v-u)k/m$, the budget increments $a_k=A(x_{k+1})-A(x_k)$ and recursion
--
--   $$C_0=c(u),\qquad C_{k+1}=\frac{a_k+C_k}{1+x_{k+1}a_k}$$
--
--   satisfy $c(v)-\varepsilon<C_m$. This gives a finite approximation used to construct near-tight canonical instances. It is a direct-grid variant of the convergence step in the proof of Lemma 4.
-- source:
--   Cui, Hamilton, Lamperski, and Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, https://doi.org/10.2139/ssrn.5178133, electronic companion ec15–ec17, proof of Lemma 4, equations (EC.21)–(EC.24); p.17, equation (10). Supporting finite-grid convergence variant.

import Definitions.Def_MinBuying_Analytic

namespace MinBuying

theorem grid_continuation_approximation (u v : ℝ) (hu : 0 ≤ u) (huv : u < v) (hv : v < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧
      let X : ℕ → ℝ := fun k => u + (v - u) * (k : ℝ) / (m : ℝ)
      let a : ℕ → ℝ := fun k => canonicalBudget (X (k + 1)) - canonicalBudget (X k)
      continuousBenchmark v - ε <
        (List.range m).foldl (fun C k => (a k + C) / (1 + X (k + 1) * a k))
          (continuousBenchmark u) := by
  sorry

end MinBuying
