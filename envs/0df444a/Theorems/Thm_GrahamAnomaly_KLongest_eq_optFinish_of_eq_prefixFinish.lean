-- Prove2me | Theorems.Thm_GrahamAnomaly_KLongest_eq_optFinish_of_eq_prefixFinish
-- name    : GrahamAnomaly.KLongest.eq_optFinish_of_eq_prefixFinish
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:47:27.118681+00:00
-- url     : https://prove2.me/theorems/64bf984e-f1e6-4284-8d42-cdd38d34dcbf
-- title:
--   Proof of Theorem 3, p. 427 — equality with the optimal prefix implies global optimality
-- statement:
--   Consider $r>0$ tasks of positive lengths on $n>0$ identical processors. Choose $0\le k\le r$ longest tasks first in a list $L$, assign each successive task to a least-loaded processor, and require the resulting first-$k$ finishing time $\omega_k$ to be minimal among assignments of those $k$ tasks. If the full finishing time $\omega(k)$ already equals $\omega_k$, then
--
--   $$
--   \omega(k)=\omega_0,
--   $$
--
--   where $\omega_0$ is the minimum finishing time for all $r$ tasks. This is the first case separated in the proof of Theorem 3.
--
--   **Formalization Note** The order of equal-length tasks and ties among least-loaded processors are unrestricted. The explicit condition $k\le r$ makes the prefix meaningful.
-- source:
--   Graham, Bounds on multiprocessing timing anomalies, SIAM J. Appl. Math. 17 (1969), p. 427, first sentence of proof of Theorem 3

import Mathlib
import Definitions.Def_GrahamAnomaly_KLongest_Model

namespace GrahamAnomaly.KLongest

theorem eq_optFinish_of_eq_prefixFinish {r n k : ℕ} (hr : 0 < r) (hn : 0 < n)
    (hk : k ≤ r) (μ : Fin r → ℝ) (hμ : ∀ j, 0 < μ j)
    (L : Fin r ≃ Fin r) (σ : Fin r → Fin n)
    (hlong : ∀ i j, (L.symm i : ℕ) < k → k ≤ (L.symm j : ℕ) → μ j ≤ μ i)
    (hσ : IsListAssignment μ L σ)
    (hopt : ∀ τ : Fin r → Fin n, prefixFinish μ L σ k ≤ prefixFinish μ L τ k) :
    WilliamsonShmoys.makespan μ σ = prefixFinish μ L σ k →
      WilliamsonShmoys.makespan μ σ = optFinish μ n := by sorry

end GrahamAnomaly.KLongest
