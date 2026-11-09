-- Prove2me | Theorems.Thm_MuonLastIterate110_Stochastic_lemma_c_4
-- name    : MuonLastIterate110.Stochastic.lemma_c_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:04:30.157889+00:00
-- url     : https://prove2.me/theorems/663be726-d104-41c1-9304-5c0070109be2
-- title:
--   Lemma C.4 — geometric-memory estimates
-- statement:
--   Let $1-\beta_t=\alpha_0t^{-q}$ with $0<\alpha_0\le1$ and $0<q<1$, and for $1\le s\le t$ let $R_{s:t}=\prod_{j=s}^t\beta_j$, with $R_{t+1:t}=1$. If $\eta_t=\eta_0t^{-p}$ with $p>0$ and $\eta_0>0$, then as $t\to\infty$
--
--   $$
--   R_{1:t}=O\bigl(e^{-ct^{1-q}}\bigr)\ \text{for some }c>0,\qquad
--   \sum_{s=2}^t R_{s:t}\eta_{s-1}=O(t^{q-p}),\qquad
--   \sum_{s=1}^t(1-\beta_s)^2R_{s+1:t}^2=O(t^{-q}).
--   $$
--
--   The implied constants depend on $\alpha_0,\eta_0,p,q$ but not on $t$.
--
--   These convolution estimates quantify how a momentum coefficient tending to one forgets the initial condition, accumulates gradient drift, and averages noise.
--
--   **Formalization Note** Each $O(\cdot)$ is an explicit bound: there is a constant $K$ (and, for the first, $c>0$ chosen first) such that the quantity is at most $K$ times the rate for all sufficiently large $t$. All three quantities are nonnegative.
--
--   Differences from the source:
--
--   - encoding: O(·) as t → ∞ with constants independent of t → ∃ K (after ∃ c > 0 for (C.13)), eventually in t: quantity ≤ K · rate; reason: this is the definition of O(·) as t → ∞ for nonnegative quantities
-- source:
--   Ping Li and Vincent Y. F. Tan, Last-Iterate Stationarity of Muon with Finitely Many Newton-Schulz Iterations, STOC 2027 submission #110 preprint (2026), source.pdf SHA-256 5362e7185a9ddcba39d1a70da110a8b04f1d179ad818e6d5d0ec73bf29586372, p.23, §C.3.1 preamble and Lemma C.4, (C.13)–(C.15); proof pp.23–24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/110.pdf

import Mathlib
import Definitions.Def_MuonLastIterate110_Stochastic_Muon

open Filter

namespace MuonLastIterate110.Stochastic

/-- Lemma C.4 (Geometric-memory estimates), pp.23–24. Let `1 − β_t = α₀ t^{−q}` with
`0 < α₀ ≤ 1`, `0 < q < 1`, and `η_t = η₀ t^{−p}` with `p > 0`, `η₀ > 0` (for `t ≥ 1`); let
`R_{s:t} = ∏_{j=s}^t β_j` with `R_{t+1:t} = 1`. Then, as `t → ∞`, with constants independent of `t`:
(C.13) `R_{1:t} = O(e^{−c t^{1−q}})` for some `c > 0`;
(C.14) `∑_{s=2}^t R_{s:t} η_{s−1} = O(t^{q−p})`;
(C.15) `∑_{s=1}^t (1 − β_s)² R_{s+1:t}² = O(t^{−q})`. -/
theorem lemma_c_4 (α₀ q η₀ p : ℝ) (hα₀ : 0 < α₀) (hα₀' : α₀ ≤ 1) (hq : 0 < q) (hq' : q < 1)
    (hη₀ : 0 < η₀) (hp : 0 < p) (β η : ℕ → ℝ)
    (hβ : ∀ t : ℕ, 1 ≤ t → β t = 1 - α₀ * (t : ℝ) ^ (-q))
    (hη : ∀ t : ℕ, 1 ≤ t → η t = η₀ * (t : ℝ) ^ (-p)) :
    (∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, ∀ᶠ t : ℕ in atTop,
        memProd β 1 t ≤ K * Real.exp (-c * (t : ℝ) ^ (1 - q))) ∧
    (∃ K : ℝ, ∀ᶠ t : ℕ in atTop,
        ∑ s ∈ Finset.Icc 2 t, memProd β s t * η (s - 1) ≤ K * (t : ℝ) ^ (q - p)) ∧
    (∃ K : ℝ, ∀ᶠ t : ℕ in atTop,
        ∑ s ∈ Finset.Icc 1 t, (1 - β s) ^ 2 * memProd β (s + 1) t ^ 2 ≤ K * (t : ℝ) ^ (-q)) := by sorry

end MuonLastIterate110.Stochastic
