-- Prove2me | Theorems.Thm_IncProx_Cyclic_footnote5_deterministic_supermartingale
-- name    : IncProx.Cyclic.footnote5_deterministic_supermartingale
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:38:30.021847+00:00
-- url     : https://prove2.me/theorems/52421cba-2f02-4648-98f3-cdfa9f9dedec
-- title:
--   Footnote 5 — deterministic supermartingale convergence: $Y_{k+1}\le Y_k-Z_k+W_k$, $\sum W_k<\infty$ $\Rightarrow$ $Y_k$ converges
-- statement:
--   Let $Y_k$, $Z_k$, $W_k$, $k=0,1,\dots$, be nonnegative real sequences such that
--   $$Y_{k+1}\le Y_k-Z_k+W_k\quad\text{for all }k,\qquad \sum_{k=0}^\infty W_k<\infty.$$
--   Then the sequence $Y_k$ converges to a real limit.
--
--   This is the deterministic special case of the supermartingale convergence theorem that the proof of Proposition 6 applies to $Y_k=\|x_{km}-x^*\|^2$.
--
--   **Formalization Note** Since $W_k\ge0$, $\sum W_k<\infty$ is Mathlib's `Summable W`.
-- source:
--   Bertsekas, Incremental Proximal Methods for Large Scale Convex Optimization, LIDS-P-2847 (rev. March 2011), footnote 5, p. 15 (used in the proof of Proposition 6)

import Mathlib

namespace IncProx.Cyclic

open Filter Topology

/-- Footnote 5 (p. 15), the deterministic special case of the supermartingale convergence theorem:
if `Y`, `Z`, `W` are nonnegative real sequences with `Y (k+1) ≤ Y k − Z k + W k` for all `k` and
`Σ W_k < ∞`, then `Y` converges. -/
theorem footnote5_deterministic_supermartingale (Y Z W : ℕ → ℝ) (hY : ∀ k, 0 ≤ Y k)
    (hZ : ∀ k, 0 ≤ Z k) (hW : ∀ k, 0 ≤ W k) (hrec : ∀ k, Y (k + 1) ≤ Y k - Z k + W k)
    (hsum : Summable W) : ∃ L : ℝ, Tendsto Y atTop (𝓝 L) := by sorry

end IncProx.Cyclic
