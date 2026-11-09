-- Prove2me | Theorems.Thm_LocalProbeMIS871_Greedy_lemma_3_8
-- name    : LocalProbeMIS871.Greedy.lemma_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T01:53:25.563199+00:00
-- url     : https://prove2.me/theorems/1649ebae-b69a-4873-afdc-d190567fb885
-- title:
--   Lemma 3.8 — A bound on X in terms of D
-- statement:
--   Let $G$ be a finite simple undirected labeled graph, let $v$ be its fixed query root, and use the cached, early-stopping greedy evaluation. Write $R$ for its fresh evaluated vertices, $U=|R|$, $\tau(u)$ for elimination times, $M_s=\sum_{u\in R}\tau(u)^s$, $X=\sum_{u\in R\setminus\{v\}}\tau(u)^s$, $D=\sum_{u\in R\setminus\{v\}}\tau(u)^s\ln(r(u)/\tau(u))$, and $c_s=\ln(s-1)-1$. Unless stated otherwise below, the root has rank $1$ and the other ranks are independent uniforms on $(0,1)$.
--
--   For every real $s>1$ there is a nonnegative measurable real random variable $L_1$ such that
--
--   $$c_sX\le sD+L_1\quad\text{almost surely},\qquad \mathbb E e^{L_1}\le2.$$
--
--   This records the inequality and exponential moment of the auxiliary random variable without assuming either as input.
--
--   Differences from the source:
--   - encoding: finite labeled graph and real rank assignment → Fin n, lexicographic real-rank/label keys, and computed cached execution; reason: zero-based labels enumerate exactly the same finite graphs and implement the source tie rule without adding a hypothesis
--   - encoding: probability and exponential expectation under the stated independent uniform ranks → the product rankLaw or its forced-root pushforward; exponential expectations use ExpBound; reason: the nonnegative Lebesgue integral and its measurability clause express the same random-variable expectation and cannot default to zero on divergence
--   - encoding: nonnegative real-valued random variable satisfying the inequality → a globally nonnegative measurable representative with the inequality almost surely under the forced-root law; reason: null inputs do not alter a random-variable inequality or its exponential moment
-- source:
--   Peter Kiss, Yuichi Yoshida, The Local Probe Complexity of Maximal Independent Set, STOC 2027 submission #871 (October 2026), p. 18, PDF p. 20, Lemma 3.8, Eq.(19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/871.pdf

import Definitions.Def_LocalProbeMIS871_Greedy_Elimination

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

namespace LocalProbeMIS871.Greedy

/-- Lemma 3.8, Eq.(19), printed p.18 / PDF20. -/
theorem lemma_3_8 {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (s : ℝ) (hs : 1 < s) :
    ∃ L₁ : (Fin n → ℝ) → ℝ, Measurable L₁ ∧ (∀ r, 0 ≤ L₁ r) ∧
      (∀ᵐ r ∂forcedLaw v, c s * X G v s r ≤ s * D G v s r + L₁ r) ∧
      ExpBound (forcedLaw v) L₁ 2 := by sorry

end LocalProbeMIS871.Greedy
