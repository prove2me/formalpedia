-- Prove2me | Theorems.Thm_KTSPBounds_subpath_averaging
-- name    : KTSPBounds.subpath_averaging
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:38:33.349778+00:00
-- url     : https://prove2.me/theorems/7cc798c3-9596-451e-b6ee-bfcf1573cc58
-- title:
--   Subpath averaging, p.9 — $l_{TSP}(k,n) \le \frac{k-1}{n} l_{TSP}(n)$
-- statement:
--   For any $n$ points and $1 \le k \le n$, the best choice of $k$ consecutive points on the optimal TSP tour gives a path of length at most $\frac{k-1}{n}$ times the tour length. Hence
--
--   $$
--   l_{TSP}(k,n) \le \frac{k-1}{n}\, l_{TSP}(n).
--   $$
--
--   The bound is deterministic. It supplies the upper bound of Theorem 2 for large $k$.
--
--   Differences from the source:
--   - encoding: the best choice of k consecutive points on the TSP tour yields an upper bound for the k-TSP → kTSPLength k x ≤ (k − 1)/n · tourLength x for every x; reason: the source states this for an arbitrary point set; the range 1 ≤ k ≤ n is the range on which both sides are defined
-- source:
--   Blanchard, Jacquillat, Jaillet, Probabilistic bounds on the k-Traveling Salesman Problem and the Traveling Repairman Problem, arXiv:2211.11063v1, §3, p.9 (second bullet); used on p.13

import Mathlib
import Definitions.Def_KTSPBounds_kTSPLength
import Definitions.Def_KTSPBounds_tourLength

namespace KTSPBounds

/-- Subpath averaging (p.9, second bullet; used again on p.13), Blanchard, Jacquillat, Jaillet, arXiv:2211.11063v1: the best
choice of `k` consecutive points on the optimal TSP tour through `n` points gives a path of length
at most `(k-1)/n · l_TSP(n)`, hence `l_TSP(k, n) ≤ (k-1)/n · l_TSP(n)`.

**Formalization Note.** Deterministic, for any `n` points and `1 ≤ k ≤ n`. -/
theorem subpath_averaging (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (x : Fin n → Plane) :
    kTSPLength k x ≤ ((k : ℝ) - 1) / (n : ℝ) * tourLength x := by sorry

end KTSPBounds
