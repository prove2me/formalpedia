-- Prove2me | Theorems.Thm_HypergraphUnreliability_FPRAS_lemma_5_1
-- name    : HypergraphUnreliability.FPRAS.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:46.403222+00:00
-- url     : https://prove2.me/theorems/08401718-de22-40ac-b090-d58aad88429f
-- title:
--   Lemma 5.1 — Safe path likelihood identity
-- statement:
--   Assume the standing context, and let $r_e>0$, $T>0$, and let $w$ be a pair of original vertices. For every bounded measurable path functional $F$,
--   $$E_{Q_w}\Bigl[e^{-\int_0^T\kappa_w(X_t)\,dt}F\Bigr]=E_P\bigl[\mathbf 1_{\{w\subseteq R(X_T)\}}F\bigr].$$
--   The integral runs through the final holding interval, including paths with no jumps and states with zero safe exit rate. The source's (5.1) is the case $r\equiv1$, $T=\log(1/p)$.
--
--   The identity corrects for protecting a pair: a proposal path is reweighted by the probability of avoiding killing transitions.
--
--   **Formalization Note** $F$ need not be nonnegative or terminal. $Q_w$ is supported on paths retaining $w$, and the indicator on the right vanishes elsewhere, so the values of $F$ on paths losing $w$ do not matter; quantifying over functionals on all paths is the source's statement.
--
--   Differences from the source:
--   - generalization: unit rates, $T=\log(1/p)$ → positive rates, any $T>0$; reason: §9.3 reuses this result at rates $r^\prime$; the printed statement is the instance $r\equiv 1$, $T=\log(1/p)$, where $e^{-rT}=p$ and `minCut (fun _ => 1)` is $\lambda$ (`minCut_one_real`)
--   - encoding: law of a continuous-time Markov chain on paths → explicit density on visited-state sequences and ordered jump times (`chainExpect`); reason: this is the density written in the proof of Lemma 5.1; the holding interval up to $T$ is included
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), Lemma 5.1, p. 6; §9.3, p. 14

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_Hypergraph
import Definitions.Def_HypergraphUnreliability_FPRAS_JumpChain
import Definitions.Def_HypergraphUnreliability_FPRAS_Contraction

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS

open LabeledHypergraph

/-- Lemma 5.1, p. 6, at positive edge rates (§9.3, p. 14). For every bounded measurable path functional
`F`, `E_{Q_w}[exp(-∫₀^T κ_w(X_t) dt) F] = E_P[1_{w ⊆ R(X_T)} F]`. The integral runs through the final
holding interval. The source's (5.1) is the case `r = 1`, `T = log(1/p)`. -/
theorem lemma_5_1 {n : ℕ} {E : Type} [Fintype E] (H : LabeledHypergraph n E) (hH : H.Standing)
    (r : E → ℝ) (hr : ∀ e, 0 < r e) (T : ℝ) (hT : 0 < T) (w : VertexPair n)
    (F : JumpPath (MarkedState n) → ℝ) (hF : IsBoundedMeasurableFunctional F) :
    chainExpect (H.safeProcessRate r w) MarkedState.init T
        (fun path => Real.exp (-JumpPath.pathIntegral (H.killRate r w) T path) * F path) =
      chainExpect (H.originalRate r) MarkedState.init T
        (fun path => (if w.1 ⊆ MarkedState.reps path.last then 1 else 0) * F path) := by sorry

end HypergraphUnreliability.FPRAS
