-- Prove2me | Theorems.Thm_LiquidDemocracy_Upward_eq_5
-- name    : LiquidDemocracy.Upward.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:48.5711+00:00
-- url     : https://prove2.me/theorems/b5ebd55c-c51e-4c51-b3ec-1d30e37f97bc
-- title:
--   (5), p. 13 — 𝔼[W^(k)_n] = Γ(n + p)Γ(k) / (Γ(p + k)Γ(n))
-- statement:
--   Let $p\in(0,1)$ and let $W^{(k)}_t$ be the size at time $t$ of a bin of the infinite Pólya urn with attachment probability $p$ that is born at time $k$ (so $W^{(k)}_k=1$, and from time $t-1$ to $t$ it grows by one with probability $pW^{(k)}_{t-1}/(t-1)$). Then for all $1\le k\le n$
--
--   $$\mathbb E\big[W^{(k)}_n\big]=\frac{\Gamma(n+p)\,\Gamma(k)}{\Gamma(p+k)\,\Gamma(n)},$$
--
--   where $\Gamma$ is the Gamma function. Together with Gautschi's inequality and Markov's inequality, this controls the bins born early in the urn.
--
--   **Formalization Note** The expectation is the integral of $w$ against the law of $W^{(k)}_n$ (finitely supported); bins are numbered from $1$, so $k\ge1$.
-- source:
--   Berinsky et al., Tracking Truth with Liquid Democracy, arXiv:2107.11868v3, p. 13, (5) (proof in Appendix B.2, p. 39)

import Mathlib
import Definitions.Def_LiquidDemocracy_Upward_Urn

namespace LiquidDemocracy.Upward

open MeasureTheory

/-- (5), p. 13 (proof in Appendix B.2, p. 39): `𝔼[W^(k)_n] = Γ(n + p)Γ(k) / (Γ(p + k)Γ(n))` for all
`1 ≤ k ≤ n`. -/
theorem eq_5 (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∫ w, (w : ℝ) ∂(wLaw p k n) =
      Real.Gamma (n + p) * Real.Gamma k / (Real.Gamma (p + k) * Real.Gamma n) := by sorry

end LiquidDemocracy.Upward
