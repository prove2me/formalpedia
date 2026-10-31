-- Prove2me | Theorems.Thm_LiquidDemocracy_Upward_early_bins
-- name    : LiquidDemocracy.Upward.early_bins
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:43.639084+00:00
-- url     : https://prove2.me/theorems/005c7a12-9954-4feb-aee6-40d7f5eaaa3c
-- title:
--   p. 13 (B.2, p. 40) — the first T^γ bins: ∑_{k ≤ T^γ} Pr[W^(k)_T > T^δ] = o(1)
-- statement:
--   Let $p\in(0,1)$, and let $\gamma,\delta$ be constants with $3/4<\gamma<1$ and $p+(1-p)\gamma<\delta<1$ (the choice made in the proof of Lemma 2). With $W^{(k)}_T$ the size at time $T$ of a bin of the infinite Pólya urn with attachment probability $p$ born at time $k$,
--
--   $$\sum_{k=1}^{\lfloor T^\gamma\rfloor}\Pr\big[W^{(k)}_T>T^\delta\big]\ \longrightarrow\ 0\qquad(T\to\infty).$$
--
--   This is the first half of the union bound in the proof of Lemma 2: the early bins are unlikely to exceed $T^\delta$ balls.
--
--   **Formalization Note** The page sums up to $T^\gamma$; the integer split is $\lfloor T^\gamma\rfloor$. Appendix B.2 restates the claim with $n^\delta$ for $T^\delta$; the statement follows p. 13.
-- source:
--   Berinsky et al., Tracking Truth with Liquid Democracy, arXiv:2107.11868v3, p. 13, proof of Lemma 2, early bins (details in Appendix B.2, p. 40)

import Mathlib
import Definitions.Def_LiquidDemocracy_Upward_Urn

namespace LiquidDemocracy.Upward

open MeasureTheory Filter Topology

/-- p. 13 (details in Appendix B.2, p. 40): with `γ, δ` as in the proof of Lemma 2
(`3/4 < γ < 1`, `p + (1 − p)γ < δ < 1`), `∑_{k=1}^{T^γ} Pr[W^(k)_T > T^δ] = o(1)`. -/
theorem early_bins (p γ δ : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hγ₁ : 3 / 4 < γ) (hγ₂ : γ < 1)
    (hδ₁ : p + (1 - p) * γ < δ) (hδ₂ : δ < 1) :
    Tendsto (fun T : ℕ => ∑ k ∈ Finset.Icc 1 ⌊(T : ℝ) ^ γ⌋₊,
      (wLaw p k T).real {w | (T : ℝ) ^ δ < (w : ℝ)}) atTop (𝓝 0) := by sorry

end LiquidDemocracy.Upward
