-- Prove2me | Theorems.Thm_LocalOccupancyIS_Glauber_three_sweep_finite
-- name    : LocalOccupancyIS.Glauber.three_sweep_finite
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T00:29:32.838228+00:00
-- url     : https://prove2.me/theorems/c854b515-6bf3-4250-bd06-9b513e49e08b
-- title:
--   Three neighborhood sweeps give the finite Glauber guarantee
-- statement:
--   Let $G$ be a finite graph on a nonempty vertex set, with maximum degree at most $\Delta\ge1$, and hereditary neighborhood $K_{t,t}$-density at most $b\ge0$, where $t\ge1$. Set $s=(b+1)^{1/(2t-1)}$ and $D=\log(\Delta/s)$. Use the fugacity and correction factor from Proposition 6. If
--
--   $$D\ge1000et,$$
--
--   then every choice of a fixed order on each neighborhood gives the averaged certificate after two and three sweeps, with occurrence bound $3\Delta$. Consequently, ordinary random-scan Glauber dynamics, from every initial independent set, has the finite expectation guarantee of Corollary 4 and the prescribed recorded-maximum repetition guarantee of Remark 2.
--
--   This is the finite dynamical step in the proof of Corollary 4. The explicit sufficient threshold makes the source's large-$D/t$ condition quantitative; the conclusion includes normalization and the stated horizon and repetition constants.
-- source:
--   Davies and Tan, Large independent sets via neighborhood block dynamics, Glauber dynamics, and local occupancy, canonical PDF November 2, 2026, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/982.pdf, pp.19–20, Proof of Corollary 4, equation (21), together with Remark 2 and Theorem 2. The numerical threshold 1000et is a sufficient explicit bound derived from the displayed estimates on pM, 8tsp, and 4tps^(1/t)M^(1-1/t).

import Definitions.Def_LocalOccupancyIS_Glauber_Execution
open LocalOccupancyIS.Glauber

theorem LocalOccupancyIS.Glauber.three_sweep_finite {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ t : ℕ) (b : ℝ)
    (hΔ : 1 ≤ Δ) (hbound : DegreeBound G Δ) (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hd : HereditaryDensity G t b) (hD : 1000*Real.exp 1*t ≤ D Δ t b)
    (w : V → List V) (hw : ∀ u, IsSweep (G.neighborFinset u) (w u)) :
    FiniteConclusion G Δ (fugacity Δ t b) (correction Δ t b) w := by sorry
