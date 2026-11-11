-- Prove2me | Theorems.Thm_NodeStableProj_Main_eq_3
-- name    : NodeStableProj.Main.eq_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:58:48.282317+00:00
-- url     : https://prove2.me/theorems/eacca181-1d4f-49d2-9877-34e0d9cf1656
-- title:
--   §3.3.2, Equation (3) — P^0_ω ≈_{ε,δ̃} P^1_ω for every ω ∈ Good_{v*}, with ε = ε̃√(2D̂ ln(1/δ̃)) + D̂ε̃(e^ε̃ − 1)/(e^ε̃ + 1)
-- statement:
--   Let $0<D<\hat D$ be integers, $\tilde\varepsilon>0$, and let $G,G'$ be fixed-vertex node-neighbouring $n$-node graphs with differing node $v^*$ isolated in $G$. For every noise vector $\omega\in\mathrm{Good}_{v^*}$ of $t(v^*)$ (with $k=(\hat D-D)/2$) and every $\tilde\delta>0$,
--   $$P^0_\omega\ \approx_{\varepsilon,\tilde\delta}\ P^1_\omega\qquad\text{for}\qquad \varepsilon=\tilde\varepsilon\sqrt{2\hat D\ln(1/\tilde\delta)}+\hat D\,\tilde\varepsilon\,\frac{e^{\tilde\varepsilon}-1}{e^{\tilde\varepsilon}+1},$$
--   where $P^0_\omega,P^1_\omega$ are the laws of $\tilde{\mathcal P}_{D,\hat D,\tilde\varepsilon}(G)_{-v^*}$ and $\tilde{\mathcal P}_{D,\hat D,\tilde\varepsilon}(G')_{-v^*}$ with $t(v^*)$'s noise fixed to $\omega$.
--
--   Averaging over $\omega\in\mathrm{Good}_{v^*}$ and accounting for the fallback gives Lemma 3.3's stability.
--
--   Differences from the source:
--   - generalization: δ̃ = δ/3 with δ ∈ (0, 1) → every δ̃ > 0; reason: Proposition 3.7 holds for any δ' > 0; δ̃ ∈ (0, 1/3) is a special case
--   - reading: v* the differing node → v* isolated in G; reason: the orientation fixed "without loss of generality" on p. 14
--   - generalization: graphs in G^n (vertex set [n]) → any common vertex set V ⊂ ℕ; reason: labels are identities; V = [n] is a special case
-- source:
--   Aden-Ali, Sealfon, Smith, Steinke, Ullman, Node Differential Privacy via Node-Stable Graph Projections, STOC 2027 submission (manuscript sha256 42f18565…), p. 17, §3.3.2, Equation (3)

import Mathlib
import Definitions.Def_NodeStableProj_Main_Projection

open MeasureTheory

namespace NodeStableProj.Main

/-- §3.3.2, Equation (3), p. 17: for fixed-vertex node-neighbouring `G, G'` with differing node
`v*` isolated in `G` and every `ω ∈ Good_{v*}`, `P^0_ω ≈_{ε,δ̃} P^1_ω` with
`ε = ε̃ √(2 D̂ ln(1/δ̃)) + D̂ ε̃ (e^{ε̃} − 1)/(e^{ε̃} + 1)`. -/
theorem eq_3 (D Dhat : ℕ) (εt : ℝ) (hD : 0 < D) (hDD : D < Dhat) (hεt : 0 < εt)
    (G G' : Graph) (vstar : ℕ) (hGG' : FixedVertexNeighbors G G' vstar)
    (hiso : G.deg vstar = 0) (ω : ℕ → ℝ)
    (hω : Good (((Dhat : ℝ) - D) / 2) G.V.card ω) (δt : ℝ) (hδt : 0 < δt) :
    PFRelease.Indist (projTildeLawFixing D Dhat εt G vstar ω)
      (projTildeLawFixing D Dhat εt G' vstar ω)
      (εt * Real.sqrt (2 * Dhat * Real.log (1 / δt)) +
        Dhat * εt * (Real.exp εt - 1) / (Real.exp εt + 1)) δt := by sorry

end NodeStableProj.Main
