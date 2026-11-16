-- Prove2me | Theorems.Thm_IntervalMaxCutEPTAS_Scheme_Supplement_lemma_7_5
-- name    : IntervalMaxCutEPTAS.Scheme.Supplement.lemma_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:37:19.013211+00:00
-- url     : https://prove2.me/theorems/a9dd13af-31ed-44b2-8ffc-c17cd49dce6f
-- title:
--   Lemma 7.5 (used in the proof of Theorem 1.3) — exact optimum and decoding
-- statement:
--   Let $Q$ be a simple graph with $n_Q$ vertices, $m_Q\ge1$ edges and $o=\operatorname{mc}(Q)$, and let $p\ge1$. Then
--
--   $$\operatorname{mc}(T_p(Q))=4p(2m_Q+n_Q+o)+n_Q^2.$$
--
--   Moreover, every target cut $S$, with $S^1,S^2$ read from the two core copies, satisfies
--
--   $$\max\{\operatorname{cut}_Q(S^1),\operatorname{cut}_Q(S^2)\}\ge o-\frac{\operatorname{mc}(T_p(Q))-\operatorname{cut}_{T_p(Q)}(S)}{4p}.$$
--
--   The exact optimum and the universal deficit inequality are one item. All arithmetic in the signed deficit is real, with the positive denominator $4p$. This quantitative connection permits an approximation gap to pass through the reduction.
--
--   Differences from the source:
--   - encoding: finite vertices and one-based copy and repetition indices → Fin n, Fin 2, and Fin p; dependent private indices; reason: these are bijective renamings, with exactly the source number of vertices and no padding
--   - encoding: the signed deficit divided by 4p → subtraction and division in ℝ after casting finite cut counts; reason: this avoids truncated natural arithmetic, and p ≥ 1 ensures the denominator is positive
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), Lemma 7.5, PDF p. 27 (printed p. 26)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Supplement_Gadget

set_option autoImplicit false

namespace IntervalMaxCutEPTAS.Scheme.Supplement

/-- Lemma 7.5, PDF 27 (printed 26). The subtraction and division in the deficit inequality
are performed in ℝ, with the positive denominator 4p. -/
theorem lemma_7_5 {n : ℕ} (Q : SimpleGraph (Fin n)) [DecidableRel Q.Adj]
    (p : ℕ) (hm : 1 ≤ Q.edgeFinset.card) (hp : 1 ≤ p) :
    mc (target Q p) = 4 * p * (2 * Q.edgeFinset.card + n + mc Q) + n ^ 2 ∧
    ∀ S : Finset (TargetVertex Q p),
      max (cutCount Q (sourceSide Q p 0 S) : ℝ) (cutCount Q (sourceSide Q p 1 S) : ℝ) ≥
        (mc Q : ℝ) - ((mc (target Q p) : ℝ) - (cutCount (target Q p) S : ℝ)) / (4 * (p : ℝ)) := by sorry

end IntervalMaxCutEPTAS.Scheme.Supplement
