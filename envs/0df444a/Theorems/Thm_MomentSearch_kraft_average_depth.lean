-- Prove2me | Theorems.Thm_MomentSearch_kraft_average_depth
-- name    : MomentSearch.kraft_average_depth
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:09:26.969958+00:00
-- url     : https://prove2.me/theorems/a2987e1d-b7de-48c9-b9fb-adbe91b3c66c
-- title:
--   Proof of Theorem 16 — Kraft's inequality and the average query depth $\ge \log_3(R+1)$
-- statement:
--   Let $n\ge2$, let $T$ be a deterministic search strategy on $[n]_0$, and let $m_0,\dots,m_R$ be $R+1$ distinct targets in $[n]_0$. Write $d_r:=q(T,m_r)$ for the number of queries $T$ uses to identify $m_r$. Then
--
--   $$
--   \sum_{r=0}^{R}3^{-d_r}\le1\qquad\text{and}\qquad \frac1{R+1}\sum_{r=0}^{R}d_r\ \ge\ \log_3(R+1).
--   $$
--
--   Viewing the strategy as a ternary tree in which every target ends at its own leaf, the first inequality is Kraft's inequality and the second follows by Jensen's inequality. It forces every strategy to spend about $\log(R+1)$ queries on one of $R+1$ candidate peaks.
--
--   Differences from the source:
--   - generalization: the proof's strategy T for U and its consecutive peaks m_r = m₀ + r → any strategy and any R + 1 distinct targets; reason: the proof's peaks are distinct targets of [n]₀, so the statement specializes to the page
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43…), App. C.3, proof of Theorem 16, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_MomentSearch_queries

namespace MomentSearch

/-- **Kraft's inequality and Jensen's inequality for a search tree**, the display in the proof of
Theorem 16, Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), App. C.3, p.27 (PDF p.29).

For a deterministic strategy `T` on `[n]₀` and `R + 1` distinct targets `m_0, …, m_R`, with
`d_r := q(T, m_r)` the number of queries `T` uses to identify `m_r`:
`∑_{r=0}^{R} 3^{−d_r} ≤ 1` and `(1/(R + 1)) ∑_{r=0}^{R} d_r ≥ log₃(R + 1)`.

**Formalization Note.** Stated for an arbitrary strategy and arbitrary distinct targets (an
injective `m : Fin (R + 1) → Fin n`); the paper uses it for the consecutive peaks
`m_r = m₀ + r`. `3^{−d}` is `(3 ^ d)⁻¹`; `log₃` is `Real.logb 3`. -/
theorem kraft_average_depth {n : ℕ} (hn : 2 ≤ n) (T : Strategy n) (R : ℕ)
    (m : Fin (R + 1) → Fin n) (hm : Function.Injective m) :
    ∑ r : Fin (R + 1), ((3 : ℝ) ^ queries T (m r : ℕ))⁻¹ ≤ 1 ∧
    Real.logb 3 ((R : ℝ) + 1) ≤
      (1 / ((R : ℝ) + 1)) * ∑ r : Fin (R + 1), (queries T (m r : ℕ) : ℝ) := by sorry

end MomentSearch
