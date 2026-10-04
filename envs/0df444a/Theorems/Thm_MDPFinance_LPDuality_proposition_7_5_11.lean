-- Prove2me | Theorems.Thm_MDPFinance_LPDuality_proposition_7_5_11
-- name    : MDPFinance.LPDuality.proposition_7_5_11
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:56:47.649421+00:00
-- url     : https://prove2.me/theorems/02dfdf39-90c7-46c0-ac4b-dfa7cf7c9106
-- title:
--   Proposition 7.5.11 — the discretization module stays close to the original as the mesh shrinks
-- statement:
--   Approximating the state space by a grid changes the operator's own contraction modulus from
--   $\alpha_b$ to a grid-dependent $\alpha_G$; this proposition bounds the damage: $\alpha_G$ never
--   exceeds $\alpha_b$ by more than a factor that tends to $1$ as the grid's own bounding function
--   $b_G$ converges uniformly to the true $b$ — i.e. as the mesh gets finer, the grid-based
--   computation's contraction property degrades only negligibly.
--
--   **Moderation note.** $\|b-b_G\|$ is finite (`hbdd`): the real supremum `mtilde` is a default $0$ when unbounded, which would make the bound $\alpha_G\le\alpha_b$ a false claim.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 221, Proposition 7.5.11

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_Bounding
import Definitions.Def_MDPFinance_LPDuality_Discretization

open MeasureTheory ProbabilityTheory Filter Topology

namespace MDPFinance.LPDuality

/-- Proposition 7.5.11 (Bäuerle–Rieder, p. 221, PDF 232). The module `\alpha_G` is bounded by
`\alpha_G \le \alpha_bm(h)`, where `m(h) \to 1` if the mesh size `h` tends to zero. Rendered
directly in terms of `\tilde m := \|b-b_G\|` (the book's own proof variable) rather than an
unformalized "mesh size `h`": `m(\tilde m) := (\alpha_b+\tilde m)/(\alpha_b(1-\tilde m))`, and
`m(\tilde m) \to 1` as `\tilde m \to 0` is the genuine content of "`m(h) \to 1` as `h \to 0`"
(the grid's own geometric mesh-size parameter is not reconstructed, see
`Def_..._Discretization.lean`'s docstring). `\|b - b_G\|` is finite (`hbdd`), so that the real
supremum `mtilde` is the book's quantity. -/
theorem proposition_7_5_11 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb) (hαb0 : 0 < αb)
    (IMc : Set (E → ℝ)) (G : GridApprox M IMc) (hbdd : ∃ K : ℝ, ∀ x, |b x - G.bG x| ≤ K)
    (hmtilde1 : mtilde b G.bG < 1) :
    alphaG M G.bG ≤ αb * ((αb + mtilde b G.bG) / (αb * (1 - mtilde b G.bG))) ∧
      Tendsto (fun mt : ℝ => (αb + mt) / (αb * (1 - mt))) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 1) := by sorry

end MDPFinance.LPDuality
