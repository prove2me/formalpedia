-- Prove2me | Theorems.Thm_HypergraphUnreliability_FPRAS_theorem_5_2
-- name    : HypergraphUnreliability.FPRAS.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:30.707618+00:00
-- url     : https://prove2.me/theorems/37bf6527-3094-414e-854a-fc86f5f409eb
-- title:
--   Theorem 5.2 — Unbiased inverse-multiplicity estimator
-- statement:
--   Assume the standing context, and let $r_e>0$, $T>0$, $N=\binom n2$, $u=u_H((e^{-r_eT})_e)$. Choose $w$ uniformly from the $N$ initial pairs, sample $Q_w$ to time $T$, and put
--   $$X=\frac{N}{\binom{K(X_T)}{2}}\exp\Bigl(-\int_0^T\kappa_w(X_t)\,dt\Bigr).$$
--   Then
--   $$EX=u,\qquad 0\le X\le Ne^{-\Lambda T},\qquad \frac{EX^2}{u^2}\le N,$$
--   the middle bound holding on every proposal path. At $r\equiv1$, $T=\log(1/p)$ this is (5.3), with $e^{-\Lambda T}=p^\lambda$.
--
--   The relative second moment is bounded by the number of vertex pairs alone, even when $u$ is exponentially small.
--
--   Differences from the source:
--   - generalization: unit rates, $T=\log(1/p)$, bound $Np^\lambda$ → positive rates, any $T>0$, bound $Ne^{-\Lambda T}$; reason: §9.3 reuses this result at rates $r^\prime$; the printed statement is the instance $r\equiv 1$, $T=\log(1/p)$, where $e^{-rT}=p$ and `minCut (fun _ => 1)` is $\lambda$ (`minCut_one_real`)
--   - encoding: law of a continuous-time Markov chain on paths → explicit density on visited-state sequences and ordered jump times (`chainExpect`); reason: this is the density written in the proof of Lemma 5.1; the holding interval up to $T$ is included
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), Theorem 5.2 and (5.2), p. 7; §9.3, p. 14

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_Hypergraph
import Definitions.Def_HypergraphUnreliability_FPRAS_JumpChain
import Definitions.Def_HypergraphUnreliability_FPRAS_Contraction

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS

open LabeledHypergraph

/-- Theorem 5.2, p. 7, at positive edge rates (§9.3, p. 14). With `w` uniform, `Q_w` run to time `T`,
`u = u_H(exp(-r T))` and `Λ` the minimum cut of `r`: `E X = u`, `0 ≤ X ≤ N exp(-Λ T)` on every proposal
path, and `E X² / u² ≤ N`. The source's (5.3) is the case `r = 1`, `T = log(1/p)`, where
`exp(-Λ T) = p^λ`. -/
theorem theorem_5_2 {n : ℕ} {E : Type} [Fintype E] (H : LabeledHypergraph n E) (hH : H.Standing)
    (r : E → ℝ) (hr : ∀ e, 0 < r e) (T : ℝ) (hT : 0 < T) :
    pairAverage (fun w => chainExpect (H.safeProcessRate r w) MarkedState.init T (estimatorX H r T w)) =
        H.unreliability (fun e => Real.exp (-(r e * T))) ∧
      (∀ (w : VertexPair n) (path : JumpPath (MarkedState n)),
        IsChainPath (H.safeProcessRate r w) MarkedState.init T path →
          0 ≤ estimatorX H r T w path ∧
            estimatorX H r T w path ≤ ((n.choose 2 : ℕ) : ℝ) * Real.exp (-(H.minCut r * T))) ∧
      pairAverage (fun w => chainExpect (H.safeProcessRate r w) MarkedState.init T
            (fun path => estimatorX H r T w path ^ 2)) /
          H.unreliability (fun e => Real.exp (-(r e * T))) ^ 2 ≤ ((n.choose 2 : ℕ) : ℝ) := by sorry

end HypergraphUnreliability.FPRAS
