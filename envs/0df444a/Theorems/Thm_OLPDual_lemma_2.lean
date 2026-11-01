-- Prove2me | Theorems.Thm_OLPDual_lemma_2
-- name    : OLPDual.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:18.052657+00:00
-- url     : https://prove2.me/theorems/3570fc58-9ab0-4775-9c05-479c0abe77d5
-- title:
--   Lemma 2, p.12 — the sample identity (11)
-- statement:
--   For a sample $u_j=(a_j,r_j)$, $j=1,\dots,n$, and any $p\in\mathbb R^m$,
--
--   $$
--   f_n(p)-f_n(p^*)=\frac1n\sum_{j=1}^n\phi(p^*,u_j)^\top(p-p^*)+\frac1n\sum_{j=1}^n\int_{a_j^\top p}^{a_j^\top p^*}\bigl(I(r_j>v)-I(r_j>a_j^\top p^*)\bigr)\,dv.
--   $$
--
--   This is the sample average version of Lemma 1, and it is the identity on which the proof of Theorem 1 rests: the first sum concentrates around $\nabla f(p^*)^\top(p-p^*)$ and the second is bounded below by a quadratic.
--
--   Differences from the source:
--   - generalization: p* the optimal solution of (7), a sample under Assumption 1 → every pstar, every d, every sample; reason: the identity is deterministic and the proof never uses optimality
--   - generalization: n the number of columns, n > m → n ≥ 1; reason: every n > m ≥ 0 has n ≥ 1, and the sums and 1/n need only a nonempty sample
--   - encoding: u = (r, a) → u = (a, r); reason: order of the pair only; same law
-- source:
--   Li–Ye, Online Linear Programming: Dual Convergence, New Algorithms, and Regret Bounds, arXiv:1909.05499v5 (19 Apr 2021), Lemma 2, display (11), p.12; proof p.33

import Mathlib
import Definitions.Def_OLPDual_Model

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OLPDual

/-- **Lemma 2**, Li–Ye, arXiv:1909.05499v5, p.12 (PDF 12), display (11): for any `p ∈ ℝ^m`,
`f_n(p) − f_n(p*) = (1/n) Σ_j φ(p*, u_j)ᵀ(p − p*)
  + (1/n) Σ_j ∫_{a_jᵀp}^{a_jᵀp*} (I(r_j > v) − I(r_j > a_jᵀp*)) dv`.
**Formalization Note** A deterministic identity: it holds for every sample and every `pstar`,
optimal or not. -/
theorem lemma_2 {m n : ℕ} (hn : 0 < n) (d : E m) (ω : Sample m n) (p pstar : E m) :
    fn d ω p - fn d ω pstar =
      (1 / (n : ℝ)) * ∑ j, ⟪phi d pstar (ω j), p - pstar⟫ +
        (1 / (n : ℝ)) * ∑ j, knightTerm (ω j).1 (ω j).2 p pstar := by sorry

end OLPDual
