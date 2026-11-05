-- Prove2me | Theorems.Thm_OmniThreshold_drop_missed_sales_term
-- name    : OmniThreshold.drop_missed_sales_term
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:35:44.749898+00:00
-- url     : https://prove2.me/theorems/85bf5240-0714-4d53-accb-0b5172549936
-- title:
--   Proof of Theorem 2, p.9, LP (2) — dropping the missed-sales term leaves the optimal solutions unchanged
-- statement:
--   Let $p\ge0$, $s_{ji}\ge0$ and $s_{ji}<c_i$ for all $i,j$, and let $A^O\le\mathcal D^O$. Write $L=\sum_i(\mathcal I_i-\min(\mathcal I_i,\mathcal D_i^P))$. Then:
--
--   1. a feasible point $(C,R,F)$ is optimal for LP (1) if and only if it is optimal for LP (2);
--   2. the optimal values $Q$ of LP (1) and $V_2$ of LP (2) satisfy
--   $$
--   Q=p\,\min\Bigl(L-\min\Bigl(\sum_iA_i^O,\,L\Bigr),\ \sum_i(\mathcal D_i^O-A_i^O)\Bigr)+V_2 .
--   $$
--
--   The proof of Theorem 2 removes the missed-sales term from the second-stage objective in this way. The value identity is the split $G=P+F$ of the expected cost into missed-sales and fulfillment parts.
--
--   Differences from the source:
--   - reading: "the optimal solution will not change" → the two programs have the same optimal solutions, and the value of LP (1) is the missed-sales term at the optimal fill plus the value of LP (2); reason: the proof uses both, since it next defines $P(S,D)$ with the optimal fill and $F(S,D)$ with LP (2)
--   - generalization: a single cancellation cost $c>\max\{s_{ji}\}$ → per-location costs with $s_{ji}<c_i$; reason: LP (1) has per-location $c_i$; the paper's assumption is the case $c_i=c$
--   - reading: penalty and shipping costs (no sign stated) → $p\ge0$, $s_{ji}\ge0$; reason: they are costs in the model of §1.1
--   - generalization: the Global Threshold's accepted orders → any accepted vector $A^O\le\mathcal D^O$; reason: the threshold's accepted orders are such a vector
-- source:
--   Jia, Karp, Ravi & Tayur, Effective Online Order Acceptance Policies for Omni-Channel Fulfillment, SSRN 3932692, proof of Theorem 2, p.9, "Similarly, we can remove the missed sales term … the optimal solution will not change", LP (2)

import Mathlib
import Definitions.Def_OmniThreshold_IsFeasible
import Definitions.Def_OmniThreshold_lp1Objective
import Definitions.Def_OmniThreshold_lp2Objective
import Definitions.Def_OmniThreshold_lp1Value
import Definitions.Def_OmniThreshold_lp2Value

namespace OmniThreshold

/-- **Proof of Theorem 2, p.9, LP (2): dropping the missed-sales term changes nothing** (Jia, Karp,
Ravi & Tayur, *Effective Online Order Acceptance Policies for Omni-Channel Fulfillment*, SSRN
3932692, proof of Theorem 2, p.9: "Similarly, we can remove the missed sales term from the
objective function of the second stage problem and the optimal solution will not change").

Under the cost assumptions `p ≥ 0`, `s_ji ≥ 0`, `s_ji < c_i`, and for accepted orders `A ≤ D^O`:
1. a feasible `x` is optimal for LP (1) if and only if it is optimal for LP (2);
2. the optimal values satisfy
   `V₁ = p · min(L − min(∑_i A_i, L), ∑_i (D_i^O − A_i)) + V₂` with
   `L = ∑_i (I_i − min(I_i, D_i^P))`.

**Formalization Note** "Optimal" is minimality of the objective among feasible points; `V₁`, `V₂`
are `lp1Value` and `lp2Value`. Clause 2 is the split `G = P + F` that the proof uses next. -/
theorem drop_missed_sales_term {n : ℕ} (I : Fin n → ℕ) (p : ℝ) (c : Fin n → ℝ)
    (s : Fin n → Fin n → ℝ) (hp : 0 ≤ p) (hs : ∀ i j, 0 ≤ s j i) (hsc : ∀ i j, s j i < c i)
    (DP DO A : Fin n → ℕ) (hA : ∀ i, A i ≤ DO i) :
    (∀ x, IsFeasible I DP A x →
      ((∀ y, IsFeasible I DP A y →
          lp1Objective p c s I DP DO A x ≤ lp1Objective p c s I DP DO A y) ↔
        (∀ y, IsFeasible I DP A y → lp2Objective c s x ≤ lp2Objective c s y))) ∧
    lp1Value p c s I DP DO A =
      p * min ((∑ i, ((I i : ℝ) - min (I i : ℝ) (DP i : ℝ))) -
          min (∑ i, (A i : ℝ)) (∑ i, ((I i : ℝ) - min (I i : ℝ) (DP i : ℝ))))
        (∑ i, ((DO i : ℝ) - (A i : ℝ))) + lp2Value c s I DP A := by sorry

end OmniThreshold
