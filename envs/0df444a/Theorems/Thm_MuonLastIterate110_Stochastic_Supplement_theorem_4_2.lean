-- Prove2me | Theorems.Thm_MuonLastIterate110_Stochastic_Supplement_theorem_4_2
-- name    : MuonLastIterate110.Stochastic.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:39:52.625587+00:00
-- url     : https://prove2.me/theorems/5bde9565-2182-40e9-9c9f-e2e700ec999b
-- title:
--   Theorem 4.2 — fixed-step full-sequence stationarity: exact gradients
-- statement:
--   Let $F:\mathbb R^{m\times n}\to\mathbb R$ be continuously differentiable, bounded below by $F_{\inf}$, with $L$-Lipschitz gradient, $L>0$ (Assumption 3.1). Use the published finite-$J$ Muon recursion from arbitrary deterministic $W_1,M_0$, with $J\ge1$, $\varepsilon>0$, constant $\beta\in[0,1)$, $\theta\in[0,1]$, and $0<\eta\le\varepsilon(1-\beta)/(4Lu_J)$. Here $u_J$ is the maximum amplification of the fixed quintic Newton–Schulz polynomial. With exact gradients $G_t=g_t=\nabla F(W_t)$, put $e_t=M_t-g_t$ and $\kappa=\varepsilon/u_J$; $D_t$ denotes the update direction. All norms are Frobenius norms.
--
--   Then all three series converge:
--
--   $$
--   \sum_{t=1}^\infty\|D_t\|^2<\infty,\qquad
--   \sum_{t=1}^\infty\|M_t-g_t\|^2<\infty,\qquad
--   \sum_{t=1}^\infty\|g_t\|^2<\infty.
--   $$
--
--   In particular, $\|\nabla F(W_t)\|\to0$. This is the constant-step exact-gradient companion to the persistent-noise goal, valid from arbitrary initialization throughout the printed parameter ranges.
--
--   Differences from the source:
--
--   - encoding: real m×n matrices with Frobenius norm → the published EuclideanSpace ℝ (Fin m × Fin n) carrier and Muon recursion; reason: its norm is the Frobenius norm; no matrix or initial condition is excluded
--   - encoding: the fixed-step setting of §4 with imposed condition (4.2) → FixedStep S L β θ η, with the exact-gradient run driven by ζ ≡ 0 where specified; reason: unfolding gives precisely J ≥ 1, ε > 0, the stated parameter ranges, schedule equalities for t ≥ 1, and the same non-strict step bound
--   - encoding: finite series of nonnegative squared norms indexed from t = 1 → Summable of the squared-norm sequences at index t + 1; reason: for nonnegative real terms this is equivalent to finiteness of the series and omits only the unused time zero
-- source:
--   Ping Li and Vincent Y. F. Tan, Last-Iterate Stationarity of Muon with Finitely Many Newton-Schulz Iterations, STOC 2027 submission #110 preprint (2026), source.pdf SHA-256 5362e7185a9ddcba39d1a70da110a8b04f1d179ad818e6d5d0ec73bf29586372, p.7, Theorem 4.2. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/110.pdf

import Mathlib
import Definitions.Def_MuonLastIterate110_Stochastic_Supplement_FixedStep

open Filter Topology MeasureTheory
open scoped ENNReal

namespace MuonLastIterate110.Stochastic.Supplement

/-- Theorem 4.2, p.7: all three square-summability conclusions (4.3) and stationarity. -/
theorem theorem_4_2 {m n : ℕ} (S : Muon m n) (L Finf β θ η : ℝ)
    (hF : Assumption31 S.F L Finf) (hfixed : FixedStep S L β θ η) :
    Summable (fun t : ℕ => ‖S.D (fun _ => 0) (t + 1)‖ ^ 2) ∧
    Summable (fun t : ℕ => ‖S.e (fun _ => 0) (t + 1)‖ ^ 2) ∧
    Summable (fun t : ℕ => ‖S.g (fun _ => 0) (t + 1)‖ ^ 2) ∧
    Tendsto (fun t => ‖S.g (fun _ => 0) t‖) atTop (𝓝 0) := by sorry

end MuonLastIterate110.Stochastic.Supplement
