-- Prove2me | Theorems.Thm_MuonLastIterate110_Stochastic_lemma_c_3
-- name    : MuonLastIterate110.Stochastic.lemma_c_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:59:30.291458+00:00
-- url     : https://prove2.me/theorems/3654d8c0-5521-4a61-8d74-35d88f7876f6
-- title:
--   Lemma C.3 — interpolation and full-sequence regularity
-- statement:
--   Let $\varepsilon\ge0$, let $h_t\ge0$, and let deterministic $\eta_t>0$ ($t\ge1$) satisfy (C.3):
--
--   $$
--   \sum_{t=1}^\infty\eta_t=\infty,\qquad\sum_{t=1}^\infty\eta_t^2<\infty .
--   $$
--
--   If there is a finite $C\ge0$ such that
--
--   $$
--   \sum_{t=1}^\infty\eta_t\psi_\varepsilon(h_t)<\infty,\qquad |h_{t+1}-h_t|\le C\eta_t\quad(t\ge1),
--   $$
--
--   then $h_t\to0$.
--
--   This is a purely deterministic statement about real sequences. It upgrades a weighted summability bound to convergence of the whole sequence, using only that the sequence varies slowly relative to the step sizes; the cases $\varepsilon=0$ and $C=0$ are included.
--
--   **Formalization Note** $\sum\eta_t=\infty$ is stated as divergence of the partial sums $\sum_{t=1}^T\eta_t$; the two convergent series have nonnegative terms and are stated as `Summable`, indexed from $t=1$.
--
--   Differences from the source:
--
--   - encoding: ∑ η_t = ∞ and series of nonnegative terms < ∞, indexed from t = 1 → partial sums ∑_{t=1}^T η_t tend to +∞; Summable of the shifted nonnegative sequences; reason: for nonnegative terms these are the same conditions
-- source:
--   Ping Li and Vincent Y. F. Tan, Last-Iterate Stationarity of Muon with Finitely Many Newton-Schulz Iterations, STOC 2027 submission #110 preprint (2026), source.pdf SHA-256 5362e7185a9ddcba39d1a70da110a8b04f1d179ad818e6d5d0ec73bf29586372, p.22, Lemma C.3, (C.9); (C.3) p.21; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/110.pdf

import Mathlib
import Definitions.Def_MuonLastIterate110_Stochastic_NewtonSchulz

open Filter Topology

namespace MuonLastIterate110.Stochastic

/-- Lemma C.3 (Interpolation and full-sequence regularity), p.22. Let `ε ≥ 0`, `h_t ≥ 0` and
deterministic `η_t > 0` (`t ≥ 1`) satisfy (C.3): `∑ η_t = ∞` and `∑ η_t² < ∞`. If for some finite
`C ≥ 0`, `∑_{t ≥ 1} η_t ψ_ε(h_t) < ∞` and `|h_{t+1} − h_t| ≤ C η_t` for all `t ≥ 1` (C.9), then
`h_t → 0`. Sequences are indexed from `t = 1`; the term at index `0` is not used. -/
theorem lemma_c_3 (ε : ℝ) (hε : 0 ≤ ε) (h η : ℕ → ℝ)
    (hh : ∀ t : ℕ, 1 ≤ t → 0 ≤ h t) (hη : ∀ t : ℕ, 1 ≤ t → 0 < η t)
    (hdiv : Tendsto (fun T : ℕ => ∑ t ∈ Finset.Icc 1 T, η t) atTop atTop)
    (hsq : Summable (fun t : ℕ => η (t + 1) ^ 2))
    (C : ℝ) (hC : 0 ≤ C)
    (hsum : Summable (fun t : ℕ => η (t + 1) * psi ε (h (t + 1))))
    (hreg : ∀ t : ℕ, 1 ≤ t → |h (t + 1) - h t| ≤ C * η t) :
    Tendsto h atTop (𝓝 0) := by sorry

end MuonLastIterate110.Stochastic
