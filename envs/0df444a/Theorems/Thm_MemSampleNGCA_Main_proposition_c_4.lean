-- Prove2me | Theorems.Thm_MemSampleNGCA_Main_proposition_c_4
-- name    : MemSampleNGCA.Main.proposition_c_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:42:23.411384+00:00
-- url     : https://prove2.me/theorems/1335f921-1134-4a0b-8762-0ddc88d2287d
-- title:
--   Proposition C.4 — P(δ_i > δ | Θ_1, …, Θ_{i−1}) ≤ 2e^{h−dδ/16} for directions drawn from r ∈ F_h
-- statement:
--   Let $\pi$ be the uniform probability measure on $S^{d-1}$, $d\ge1$. Let $q\ge1$ be an integer, $h\ge0$, $8q/d\le\delta\le1/2$, and $r\in F_h$, i.e. $r\ge0$ measurable with $\int r\,d\pi=1$ and $r\le e^h$. Let $1\le i\le q$ and fix $\theta_1,\dots,\theta_{i-1}\in S^{d-1}$. If $\Theta_i\sim r\,d\pi$, then $\delta_i=\|\mathrm{Proj}_{\mathrm{span}(\theta_1,\dots,\theta_{i-1})}\Theta_i\|_2^2$ satisfies
--   $$P\big(\delta_i>\delta\big)=\int_{S^{d-1}}\mathbf 1\big\{\|\mathrm{Proj}_{\mathrm{span}(\theta_1,\dots,\theta_{i-1})}\theta\|_2^2>\delta\big\}\,r(\theta)\,\pi(d\theta)\le2e^{h-d\delta/16}.$$
--   This is the paper's conditional bound for $\Theta_1,\dots,\Theta_q$ i.i.d. from $r\,d\pi$, with the conditional law of $\Theta_i$ given its predecessors written out.
--
--   A direction drawn from a diffuse density on the sphere is unlikely to lie close to the span of a few earlier directions. This is what makes the high moments of NGCA mixtures small (Proposition C.3).
--
--   Differences from the source:
--   - generalization: under the assumptions of Proposition C.3 (A satisfies (A1)–(A2)) → no assumption on A; reason: A does not occur in the statement, and the proof uses only r ≤ e^h
--   - encoding: P(δ_i > δ | Θ_1, …, Θ_{i−1}) for Θ_1, …, Θ_q i.i.d. from r dπ → the (r dπ)-measure of {θ : ‖Proj_{span(θ_1,…,θ_{i−1})} θ‖² > δ}, for every fixed θ_1, …, θ_{i−1} ∈ S^{d−1}; reason: Θ_i is independent of its predecessors with law r dπ, so the conditional probability is this function of the predecessors; a bound for every tuple gives the almost-sure bound
--   - encoding: δ_i → ‖Proj_{span(Θ_1,…,Θ_{i−1})} Θ_i‖² with the orthogonal projection Submodule.starProjection; reason: the definition of Step 4 (p. 26) (see INSIGHTS I1 for Step 2's typo)
--   - encoding: π uniform on S^{d−1}; F_h → (volume.toSphere) normalized to mass 1 (sphereUnif); measurable ℝ≥0∞-valued densities; reason: Mathlib's surface measure; densities must be measurable
--   - encoding: d implicit → d ≥ 1; reason: 8q/d is undefined at d = 0
-- source:
--   Pensia, Gupta, Verchand, Sharan, Vedantam, Memory-Sample Tradeoffs in High-Dimensional Statistics, STOC 2027 submission (manuscript sha256 ac94994a…), p. 26 (PDF 28), Proposition C.4; proof p. 27 (PDF 29)

import Mathlib
import Definitions.Def_MemSampleNGCA_Main_Streaming
import Definitions.Def_MemSampleNGCA_Main_NGCA
import Definitions.Def_MemSampleNGCA_Main_Framework

open MeasureTheory
open scoped ENNReal

namespace MemSampleNGCA.Main

/-- Proposition C.4 (p. 26, PDF 28), with the conditional law written out: for an integer
`q ≥ 1`, `h ≥ 0`, `8q/d ≤ δ ≤ 1/2`, a density `r ∈ F_h` on `S^{d−1}`, `1 ≤ i ≤ q` and any fixed
predecessors `θ_1, …, θ_{i−1} ∈ S^{d−1}`, a direction `Θ_i ∼ r dπ` satisfies
`P(‖Proj_{span(θ_1,…,θ_{i−1})} Θ_i‖² > δ) ≤ 2 e^{h − dδ/16}`. -/
theorem proposition_c_4 (d q : ℕ) (hq : 1 ≤ q) (h δ : ℝ) (hh : 0 ≤ h) (hd : 1 ≤ d)
    (hδ₁ : (8 * q : ℝ) / d ≤ δ) (hδ₂ : δ ≤ 1 / 2)
    (r : Metric.sphere (0 : Rd d) 1 → ℝ≥0∞) (hr : r ∈ Fh (sphereUnif d) h)
    (i : ℕ) (hi₁ : 1 ≤ i) (hi₂ : i ≤ q) (θs : Fin (i - 1) → Metric.sphere (0 : Rd d) 1) :
    ∫⁻ θ in {θ : Metric.sphere (0 : Rd d) 1 |
        δ < ‖(Submodule.span ℝ (Set.range fun j => (θs j : Rd d))).starProjection (θ : Rd d)‖ ^ 2},
        r θ ∂(sphereUnif d) ≤
      ENNReal.ofReal (2 * Real.exp (h - d * δ / 16)) := by sorry

end MemSampleNGCA.Main
