-- Prove2me | Theorems.Thm_LiquidDemocracy_Upward_bin_domination
-- name    : LiquidDemocracy.Upward.bin_domination
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:46.992808+00:00
-- url     : https://prove2.me/theorems/7db2faf0-ba32-4e73-ba1d-aa93f441cf9d
-- title:
--   p. 13, before (4) — W^(k)_t stochastically dominates U^(k)_t
-- statement:
--   In the infinite Pólya urn with attachment probability $p\in(0,1)$, let $U^{(k)}_t$ be the size at time $t$ of the $k$-th bin to be born and $W^{(k)}_t$ the size at time $t$ of a bin born at time $k$. For all $1\le k\le t$ and every threshold $x\in\mathbb R$,
--
--   $$\Pr\big[U^{(k)}_t>x\big]\le\Pr\big[W^{(k)}_t>x\big],$$
--
--   that is, $W^{(k)}_t$ stochastically dominates $U^{(k)}_t$: the $k$-th bin can be born only at time $k$ or later. This lets the analysis of the largest bin replace each $U^{(k)}_T$ by $W^{(k)}_T$, which reduces Lemma 2 to $\sum_{k=1}^T\Pr[W^{(k)}_T>T^\delta]=o(1)$ (equation (4)).
--
--   **Formalization Note** The page writes "for $k>t$" in the definition of $W^{(k)}_t$ where $t>k$ is meant; the definition follows the intended reading. Bins are numbered from 1.
-- source:
--   Berinsky et al., Tracking Truth with Liquid Democracy, arXiv:2107.11868v3, p. 13, stochastic domination of U^(k)_t by W^(k)_t, before (4)

import Mathlib
import Definitions.Def_LiquidDemocracy_Upward_Urn

namespace LiquidDemocracy.Upward

open MeasureTheory

/-- p. 13, before (4): `W^(k)_t` stochastically dominates `U^(k)_t` for all `k` and `t`:
`Pr[U^(k)_t > x] ≤ Pr[W^(k)_t > x]` for every threshold `x`. -/
theorem bin_domination (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (k t : ℕ) (hk : 1 ≤ k) (hkt : k ≤ t)
    (x : ℝ) :
    (urnLaw p t).real {s | x < (binSize s k : ℝ)} ≤ (wLaw p k t).real {w | x < (w : ℝ)} := by sorry

end LiquidDemocracy.Upward
