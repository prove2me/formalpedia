-- Prove2me | Theorems.Thm_NodeStableProj_Main_svt_detector_privacy
-- name    : NodeStableProj.Main.svt_detector_privacy
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:58:24.690734+00:00
-- url     : https://prove2.me/theorems/162be3e2-8320-450f-947f-9f0d0d40d9b0
-- title:
--   §3.3.2 — the SVT detector is (ε̃, 0)-DP in the continual-release model with adaptively chosen inputs
-- statement:
--   Let $\tau\in\mathbb R$ and $\tilde\varepsilon>0$. The SVT detector of Algorithm 2 with threshold $\tau$ and parameter $\tilde\varepsilon$, viewed as an interactive mechanism that receives increments $b\in[0,1]$ one at a time and outputs its flag after each, is
--   $$(\tilde\varepsilon,0)\text{-differentially private in the continual-release model with adaptive inputs:}$$
--   for every adaptive adversary that sends it pairs of increment streams differing in at most one update, the laws of the adversary's output under the two choices of stream are $(\tilde\varepsilon,0)$-indistinguishable.
--
--   The paper cites this fact ([LSL17, Theorem 2] non-adaptively, [JRSS23] adaptively) and applies it to each detector $t(u)$ inside the concurrent composition of Claim 3.8.
--
--   Differences from the source:
--   - encoding: continual-release (ε̃,0)-DP with adaptively chosen inputs under single-update changes → IsContinualDP: every adversary (any output space, measurable output) forming a 1-sparse composition with the single mechanism; reason: this is the game of [JRSS23]: one differing update, adaptive choice, the adversary's view compared
--   - encoding: Laplace noises of the detector → η = Lap(2/ε̃)-inverse-CDF of tape cell 0, ξ_ℓ = Lap(4/ε̃)-inverse-CDF of tape cell ℓ; reason: the same law, drawn from a uniform tape
--   - encoding: increments b ∈ [0, 1] → inputs of type unitInterval; reason: same instances
-- source:
--   Aden-Ali, Sealfon, Smith, Steinke, Ullman, Node Differential Privacy via Node-Stable Graph Projections, STOC 2027 submission (manuscript sha256 42f18565…), p. 13 §3.1 and p. 17 §3.3.2 (cited from [LSL17, Theorem 2] and [JRSS23])

import Mathlib
import Definitions.Def_NodeStableProj_Main_Concurrent

open MeasureTheory

namespace NodeStableProj.Main

/-- §3.3.2 (p. 17) and §3.1 (p. 13): the SVT detector (Algorithm 2) with any threshold `τ` and
parameter `ε̃ > 0` is `(ε̃, 0)`-differentially private in the continual-release model with
adaptively chosen inputs, under single-update changes to its increment stream. -/
theorem svt_detector_privacy (τ εt : ℝ) (hεt : 0 < εt) :
    IsContinualDP (svtMechanism τ εt) εt := by sorry

end NodeStableProj.Main
