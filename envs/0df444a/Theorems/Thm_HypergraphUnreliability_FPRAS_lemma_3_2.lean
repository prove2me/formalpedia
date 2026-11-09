-- Prove2me | Theorems.Thm_HypergraphUnreliability_FPRAS_lemma_3_2
-- name    : HypergraphUnreliability.FPRAS.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:35.008951+00:00
-- url     : https://prove2.me/theorems/1e6c00f4-b5e7-49a4-a0c5-08ace3495c85
-- title:
--   Lemma 3.2 — Contraction law equals independent edge failures
-- statement:
--   Assume the standing context: $n\ge2$, $H$ connected, every edge with at least two vertices. Let $r_e>0$ and $T>0$, and let each copy of $e$ contract at rate $r_e/2$. Then at time $T$ the blocks under the original process $P$ have the distribution of the connected components after independent edge failures with probabilities $e^{-r_eT}$. In particular,
--   $$P_P[K(X_T)\ge2]=u_H\bigl((e^{-r_eT})_e\bigr).$$
--
--   The source's statement is the case $r\equiv1$, $T=\log(1/p)$, where the failure probability is $p$ and the display is (3.1).
--
--   This turns disconnection into the survival of at least two representatives along a Markov chain.
--
--   Differences from the source:
--   - generalization: unit rates, $T=\log(1/p)$, common failure probability $p$ → positive rates $r$ and any $T>0$, failure probabilities $e^{-r_eT}$; reason: §9.3 reuses this result at rates $r^\prime$; the printed statement is the instance $r\equiv 1$, $T=\log(1/p)$, where $e^{-rT}=p$ and `minCut (fun _ => 1)` is $\lambda$ (`minCut_one_real`)
--   - encoding: law of a continuous-time Markov chain on paths → explicit density on visited-state sequences and ordered jump times (`chainExpect`); reason: this is the density written in the proof of Lemma 5.1; the holding interval up to $T$ is included
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), Lemma 3.2, p. 5; §9.3, p. 14

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_Hypergraph
import Definitions.Def_HypergraphUnreliability_FPRAS_JumpChain
import Definitions.Def_HypergraphUnreliability_FPRAS_Contraction

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS

open LabeledHypergraph

/-- Lemma 3.2, p. 5, at positive edge rates (§9.3, p. 14). Each copy of `e` has rate `r e / 2`. At time
`T` the blocks of the original process have the distribution of the connected components after
independent edge failures with probabilities `exp(-r e T)`, and
`P[K(X_T) ≥ 2] = u_H(exp(-r T))`. The source's Lemma 3.2 is the case `r = 1`, `T = log(1/p)`. -/
theorem lemma_3_2 {n : ℕ} {E : Type} [Fintype E] (H : LabeledHypergraph n E) (hH : H.Standing)
    (r : E → ℝ) (hr : ∀ e, 0 < r e) (T : ℝ) (hT : 0 < T) :
    (∀ π : Setoid (Fin n),
      chainExpect (H.originalRate r) MarkedState.init T
          (fun path => if MarkedState.blocks path.last = π then 1 else 0) =
        prodProb (fun e => Real.exp (-(r e * T))) (fun D => H.components D = π)) ∧
    chainExpect (H.originalRate r) MarkedState.init T
        (fun path => if 2 ≤ MarkedState.K path.last then 1 else 0) =
      H.unreliability (fun e => Real.exp (-(r e * T))) := by sorry

end HypergraphUnreliability.FPRAS
