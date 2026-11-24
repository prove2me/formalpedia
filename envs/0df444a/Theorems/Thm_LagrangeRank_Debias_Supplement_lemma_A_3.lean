-- Prove2me | Theorems.Thm_LagrangeRank_Debias_Supplement_lemma_A_3
-- name    : LagrangeRank.Debias.Supplement.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:49:45.577828+00:00
-- url     : https://prove2.me/theorems/7ff102a9-2eaf-4a98-b060-c31c2fae8d69
-- title:
--   Lemma A.3 (corrected: working event and inverse action) — both conditional remainder bounds
-- statement:
--   Let $K>0$ be fixed. There is a constant $C=C(K)>0$, uniform in the number of items $n$, repetitions $L$, graph and outcomes, such that on the conditional working event of (A.8)–(A.12), intersected with the initial-estimator event of Lemma 3.1, the actual remainders $I_1,I_2$ in (A.7) satisfy
--   $$\|I_1\|_\infty\le C\frac{\sqrt n\log n}{\sqrt p\,L},\qquad
--   \|I_2\|_\infty\le C\frac{\log n}{\sqrt n\,pL}.$$
--   Here $p\in(0,1]$, $n\ge2$, $L\ge1$, $np\ge\log n$, and the regularization coefficient is positive. Every input is the concrete BTL loss, MLE and inverse; the remainders are not free vectors.
--
--   The bounds are pointwise on that event, so also apply after conditioning on any graph. The corrected inverse bound controls its action on vectors $(v,0)$, which is what (A.7) uses. This retains both rates, with the second square root covering only $n$.
--
--   Differences from the source:
--   - correction: (A.11) identifies the whole inverse norm with the reciprocal nonzero Hessian eigenvalue → control of the inverse on zero-sum (v,0), rather than the false whole-space equality; reason: p. 70 displays the additional eigenvalues ±√n; see DISPROOF.md C1, with n=25 giving 1/5 versus 4/25
--   - reading: the conditional working event in Lemma A.3 → intersection with the Lemma 3.1 initial-estimator event explicitly used in (C.2), p. 47; reason: the source proof uses the initial-error rate to multiply (A.10); this is not a hypothesis substituted for the MLE in Theorem 3.2
--   - generalization: asymptotic bounds for the BTL sequence on its working event → a deterministic dimension-uniform bound for every realization satisfying the displayed inequalities; reason: the norm calculation uses only these inequalities and np≥log n; applying it on the source working event gives both source bounds
-- source:
--   Liu, Fang, Lu, Lagrangian Inference for Ranking Problems, arXiv:2110.00151v1, p. 42, Lemma A.3

import Mathlib
import Definitions.Def_LagrangeRank_Debias_Supplement_BTL

namespace LagrangeRank.Debias.Supplement

open MeasureTheory ProbabilityTheory Matrix Filter Topology
/-- Corrected conditional remainder bounds; uniformly over dimensions and realizations. -/
theorem lemma_A_3 (K : ℝ) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n L : ℕ) (p c : ℝ) (s : Data n L) (θ : Vec n),
      2 ≤ n → 0 < L → 0 < p → p ≤ 1 → 0 < c → Real.log n ≤ n * p →
      SourceBounds p c K s θ →
      ‖I1 p c s θ‖ ≤ C * Real.sqrt n * Real.log n / (Real.sqrt p * L) ∧
      ‖I2 p c s θ‖ ≤ C * Real.log n / (Real.sqrt n * p * L) := by sorry

end LagrangeRank.Debias.Supplement
