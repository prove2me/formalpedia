-- Prove2me | Theorems.Thm_HypergraphUnreliability_FPRAS_lemma_4_1
-- name    : HypergraphUnreliability.FPRAS.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:47.177894+00:00
-- url     : https://prove2.me/theorems/99757f88-d7bf-4f62-99cc-8cbc5b76bfa8
-- title:
--   Lemma 4.1 — Paired representative hazard
-- statement:
--   Assume the standing context, and let $r_e>0$. Let $x$ be any marked state in which both labels of $w=\{a,b\}$ are representatives, with blocks $A,B$. Then
--   $$\kappa_w(x)\ \ge\ \frac12\Bigl(\sum_{e\in\partial_H A}r_e+\sum_{e\in\partial_H B}r_e\Bigr)\ \ge\ \Lambda .$$
--
--   At $r\equiv1$ this is (4.3), $\kappa_w(x)\ge\lambda$, and in general it is (9.6). The statement covers every marked state, not only reachable ones.
--
--   It controls the estimator and makes the cemetery rate $\kappa_w-\Lambda$ nonnegative.
--
--   Differences from the source:
--   - generalization: unit rates, $\kappa_w(x)\ge\lambda$ → positive rates, with the intermediate bound of (9.6) as well; reason: §9.3 reuses this result at rates $r^\prime$; the printed statement is the instance $r\equiv 1$, $T=\log(1/p)$, where $e^{-rT}=p$ and `minCut (fun _ => 1)` is $\lambda$ (`minCut_one_real`)
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), Lemma 4.1, p. 5; (9.6), p. 14

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_Hypergraph
import Definitions.Def_HypergraphUnreliability_FPRAS_JumpChain
import Definitions.Def_HypergraphUnreliability_FPRAS_Contraction

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS

open LabeledHypergraph

/-- Lemma 4.1, p. 5, at positive edge rates, in the two-step form of (9.6), p. 14. In every marked
state `x` in which both labels of `w = {a, b}` survive, with protected blocks `A, B`,
`κ_w(x) ≥ ½ (∑_{e ∈ ∂A} r e + ∑_{e ∈ ∂B} r e) ≥ Λ`. The source's (4.3) is the case `r = 1`, in which
`Λ` is `λ` (see `minCutCount`). -/
theorem lemma_4_1 {n : ℕ} {E : Type} [Fintype E] (H : LabeledHypergraph n E) (hH : H.Standing)
    (r : E → ℝ) (hr : ∀ e, 0 < r e) (x : MarkedState n) (w : VertexPair n) (a b : Fin n)
    (hw : w.1 = {a, b}) (hab : a ≠ b) (hsurv : w.1 ⊆ MarkedState.reps x) :
    (1 / 2) * (H.cutWeight r (MarkedState.block x a) + H.cutWeight r (MarkedState.block x b)) ≤
        H.killRate r w x ∧
      H.minCut r ≤
        (1 / 2) * (H.cutWeight r (MarkedState.block x a) + H.cutWeight r (MarkedState.block x b)) ∧
      H.minCut r ≤ H.killRate r w x := by sorry

end HypergraphUnreliability.FPRAS
