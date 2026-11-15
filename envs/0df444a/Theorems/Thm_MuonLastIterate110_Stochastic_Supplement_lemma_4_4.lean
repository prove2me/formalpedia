-- Prove2me | Theorems.Thm_MuonLastIterate110_Stochastic_Supplement_lemma_4_4
-- name    : MuonLastIterate110.Stochastic.Supplement.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:38:47.152794+00:00
-- url     : https://prove2.me/theorems/1bd27d20-b363-4b9f-b69c-e37d61e8e229
-- title:
--   Lemma 4.4 — momentum tracking
-- statement:
--   Let $F:\mathbb R^{m\times n}\to\mathbb R$ be continuously differentiable, bounded below by $F_{\inf}$, with $L$-Lipschitz gradient, $L>0$ (Assumption 3.1). Use the published finite-$J$ Muon recursion from arbitrary deterministic $W_1,M_0$, with $J\ge1$, $\varepsilon>0$, constant $\beta\in[0,1)$, $\theta\in[0,1]$, and $0<\eta\le\varepsilon(1-\beta)/(4Lu_J)$. Here $u_J$ is the maximum amplification of the fixed quintic Newton–Schulz polynomial. With exact gradients $G_t=g_t=\nabla F(W_t)$, put $e_t=M_t-g_t$ and $\kappa=\varepsilon/u_J$; $D_t$ denotes the update direction. All norms are Frobenius norms.
--
--   For every $t\ge1$,
--
--   $$
--   \|e_{t+1}\|^2\le\frac{1+\beta}{2}\|e_t\|^2+\frac{\beta(1+\beta)L^2\eta^2}{1-\beta}\|D_t\|^2.
--   $$
--
--   This controls tracking error in terms of the preceding tracking error and the update direction. It includes $\beta=0$ and retains the section's imposed step condition.
--
--   Differences from the source:
--
--   - encoding: real m×n matrices with Frobenius norm → the published EuclideanSpace ℝ (Fin m × Fin n) carrier and Muon recursion; reason: its norm is the Frobenius norm; no matrix or initial condition is excluded
--   - encoding: the fixed-step setting of §4 with imposed condition (4.2) → FixedStep S L β θ η, with the exact-gradient run driven by ζ ≡ 0 where specified; reason: unfolding gives precisely J ≥ 1, ε > 0, the stated parameter ranges, schedule equalities for t ≥ 1, and the same non-strict step bound
-- source:
--   Ping Li and Vincent Y. F. Tan, Last-Iterate Stationarity of Muon with Finitely Many Newton-Schulz Iterations, STOC 2027 submission #110 preprint (2026), source.pdf SHA-256 5362e7185a9ddcba39d1a70da110a8b04f1d179ad818e6d5d0ec73bf29586372, p.8, Lemma 4.4. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/110.pdf

import Mathlib
import Definitions.Def_MuonLastIterate110_Stochastic_Supplement_FixedStep

open Filter Topology MeasureTheory
open scoped ENNReal

namespace MuonLastIterate110.Stochastic.Supplement

/-- Lemma 4.4, p.8; the case β = 0 is included. -/
theorem lemma_4_4 {m n : ℕ} (S : Muon m n) (L Finf β θ η : ℝ)
    (hF : Assumption31 S.F L Finf) (hfixed : FixedStep S L β θ η) (t : ℕ) (ht : 1 ≤ t) :
    ‖S.e (fun _ => 0) (t + 1)‖ ^ 2 ≤
      (1 + β) / 2 * ‖S.e (fun _ => 0) t‖ ^ 2 +
        β * (1 + β) * L ^ 2 * η ^ 2 / (1 - β) * ‖S.D (fun _ => 0) t‖ ^ 2 := by sorry

end MuonLastIterate110.Stochastic.Supplement
