-- Prove2me | Theorems.Thm_LiquidDemocracy_Upward_late_bins
-- name    : LiquidDemocracy.Upward.late_bins
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:47.620009+00:00
-- url     : https://prove2.me/theorems/9717c453-d3d0-4eab-8872-8358bba87ea4
-- title:
--   pp. 13–15 — the last T − T^γ bins: ∑_{k > T^γ} Pr[W^(k)_T > T^δ] = o(1)
-- statement:
--   Let $p\in(0,1)$ and $3/4<\gamma<1$, $p+(1-p)\gamma<\delta<1$ as in the proof of Lemma 2. With $W^{(k)}_T$ the size at time $T$ of a bin of the infinite Pólya urn with attachment probability $p$ born at time $k$,
--
--   $$\sum_{k=\lfloor T^\gamma\rfloor+1}^{T}\Pr\big[W^{(k)}_T>T^\delta\big]\ \longrightarrow\ 0\qquad(T\to\infty).$$
--
--   This is the second half of the union bound in the proof of Lemma 2: bins born after time $T^\gamma$ are unlikely to exceed $T^\delta$ balls.
--
--   **Formalization Note** The integer split is $\lfloor T^\gamma\rfloor$. The paper bounds each term by $o(1/T)$ through a comparison process and a cited rate of convergence to a Beta law; the statement is only the sum bound.
-- source:
--   Berinsky et al., Tracking Truth with Liquid Democracy, arXiv:2107.11868v3, pp. 13–15, proof of Lemma 2, late bins

import Mathlib
import Definitions.Def_LiquidDemocracy_Upward_Urn

namespace LiquidDemocracy.Upward

open MeasureTheory Filter Topology

/-- pp. 13–15: with `γ, δ` as in the proof of Lemma 2 (`3/4 < γ < 1`, `p + (1 − p)γ < δ < 1`),
`∑_{k=T^γ+1}^{T} Pr[W^(k)_T > T^δ] = o(1)`. -/
theorem late_bins (p γ δ : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hγ₁ : 3 / 4 < γ) (hγ₂ : γ < 1)
    (hδ₁ : p + (1 - p) * γ < δ) (hδ₂ : δ < 1) :
    Tendsto (fun T : ℕ => ∑ k ∈ Finset.Ioc ⌊(T : ℝ) ^ γ⌋₊ T,
      (wLaw p k T).real {w | (T : ℝ) ^ δ < (w : ℝ)}) atTop (𝓝 0) := by sorry

end LiquidDemocracy.Upward
