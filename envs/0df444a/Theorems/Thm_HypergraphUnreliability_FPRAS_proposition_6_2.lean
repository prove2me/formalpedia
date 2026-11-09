-- Prove2me | Theorems.Thm_HypergraphUnreliability_FPRAS_proposition_6_2
-- name    : HypergraphUnreliability.FPRAS.proposition_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:58.809129+00:00
-- url     : https://prove2.me/theorems/a5474413-6493-4dcb-8df2-a410b278a90f
-- title:
--   Proposition 6.2 — Normalized absorbing-process moments
-- statement:
--   Assume the standing context, and let $r_e>0$, $T>0$. Let $\Lambda$ be the minimum cut of $r$ and $\mu=e^{\Lambda T}u_H((e^{-r_eT})_e)$. Choose $w$ uniformly and run $R_w$ to time $T$, and put $Y=g(X_T)$. Then
--   $$EY=\mu,\qquad 0\le Y\le N,\qquad EY^2\le N\mu,\qquad 1\le\mu\le N.$$
--
--   At $r\equiv1$, $T=\log(1/p)$, $\mu=u_H(p)/p^\lambda$ and this is (6.5) with (6.1). At $r=r^\prime$, $T=1$ it is (9.7).
--
--   Normalizing replaces a transcendental likelihood by a survival probability, and the reward is then rational and bounded.
--
--   Differences from the source:
--   - generalization: unit rates, $T=\log(1/p)$ → positive rates, any $T>0$, covering (9.7); reason: §9.3 reuses this result at rates $r^\prime$; the printed statement is the instance $r\equiv 1$, $T=\log(1/p)$, where $e^{-rT}=p$ and `minCut (fun _ => 1)` is $\lambda$ (`minCut_one_real`)
--   - generalization: (6.5) lists the three moments; $1\le\mu\le N$ is the separate display (6.1) → the conclusion also contains $1\le\mu\le N$; reason: (6.1) and (9.7) state it and the later steps use it
--   - encoding: law of a continuous-time Markov chain on paths → explicit density on visited-state sequences and ordered jump times (`chainExpect`); reason: this is the density written in the proof of Lemma 5.1; the holding interval up to $T$ is included
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), Proposition 6.2, p. 8; (6.1), p. 7; (9.7), p. 14

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_Hypergraph
import Definitions.Def_HypergraphUnreliability_FPRAS_JumpChain
import Definitions.Def_HypergraphUnreliability_FPRAS_Contraction

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS

open LabeledHypergraph

/-- Proposition 6.2, p. 8, at positive edge rates, in the form (9.7), p. 14. Choose `w` uniformly and run
`R_w`, with cemetery rate `κ_w - Λ`, to time `T`, and put `Y = g(X_T)`. With
`μ = exp(Λ T) u_H(exp(-r T))`: `E Y = μ`, `0 ≤ Y ≤ N`, `E Y² ≤ N μ` and `1 ≤ μ ≤ N`. The source's (6.5)
and (6.1) are the case `r = 1`, `T = log(1/p)`, where `μ = u_H(p)/p^λ`; (9.7) is `r = r′`, `T = 1`. -/
theorem proposition_6_2 {n : ℕ} {E : Type} [Fintype E] (H : LabeledHypergraph n E) (hH : H.Standing)
    (r : E → ℝ) (hr : ∀ e, 0 < r e) (T : ℝ) (hT : 0 < T) :
    pairAverage (fun w => chainExpect (H.absorbingRate r (H.minCut r) w)
        (some MarkedState.init) T (fun path => terminalReward path.last)) =
        Real.exp (H.minCut r * T) * H.unreliability (fun e => Real.exp (-(r e * T))) ∧
      (∀ a : Option (MarkedState n), (0 : ℝ) ≤ terminalReward a ∧
        (terminalReward a : ℝ) ≤ ((n.choose 2 : ℕ) : ℝ)) ∧
      pairAverage (fun w => chainExpect (H.absorbingRate r (H.minCut r) w)
        (some MarkedState.init) T (fun path => (terminalReward path.last : ℝ) ^ 2)) ≤
        ((n.choose 2 : ℕ) : ℝ) *
          (Real.exp (H.minCut r * T) * H.unreliability (fun e => Real.exp (-(r e * T)))) ∧
      1 ≤ Real.exp (H.minCut r * T) * H.unreliability (fun e => Real.exp (-(r e * T))) ∧
      Real.exp (H.minCut r * T) * H.unreliability (fun e => Real.exp (-(r e * T))) ≤
        ((n.choose 2 : ℕ) : ℝ) := by sorry

end HypergraphUnreliability.FPRAS
