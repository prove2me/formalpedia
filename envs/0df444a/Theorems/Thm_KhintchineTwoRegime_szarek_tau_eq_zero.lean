-- Prove2me | Theorems.Thm_KhintchineTwoRegime_szarek_tau_eq_zero
-- name    : KhintchineTwoRegime.szarek_tau_eq_zero
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:03:11.238854+00:00
-- url     : https://prove2.me/theorems/0332eeec-b6fa-4ee6-9e10-8f4560e7ca6c
-- title:
--   Distance zero characterizes the two-coordinate Szarek extremal set
-- statement:
--   Let $n\ge2$ and $x\in\mathbb R^n$. Define the distance to the Szarek extremal set as in eq. (5) of the paper,
--   $$
--   \tau(x)=\min_{i<j,\ \sigma,\sigma'\in\{\pm1\}}
--   \left\|x+\frac{\sigma e_i+\sigma'e_j}{\sqrt2}\right\|_2.
--   $$
--   If $\tau(x)=0$, then there are distinct coordinates $i,j$ such that
--   $$
--   |x_i|=|x_j|=\frac1{\sqrt2}.
--   $$
--
--   For a unit vector, these two coordinates necessarily exhaust the squared norm, so this identifies the equality case in the sharp Khintchine lower bound. The result is also useful for proving the uniqueness clauses of the two-regime minimization theorems.
--
--   **Formalization Note** The distance is the published finite-minimum definition `KhintchineTwoRegime.Supplement.tau`, with $0$-based indices and `l2Norm`. Signs are encoded by `Bool`.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §1, p.1 (Szarek equality case) and §2, eq. (5), p.4 (distance to the extremal set).

import Mathlib
import Definitions.Def_KhintchineTwoRegime_Supplement_tau
import Definitions.Def_HighDimProb_SparseRecovery_L2Norm

theorem KhintchineTwoRegime.szarek_tau_eq_zero {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hτ : KhintchineTwoRegime.Supplement.tau hn x = 0) :
    ∃ i j : Fin n, i ≠ j ∧ |x i| = 1 / Real.sqrt 2 ∧ |x j| = 1 / Real.sqrt 2 := by sorry
