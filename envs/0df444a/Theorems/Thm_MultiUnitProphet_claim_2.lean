-- Prove2me | Theorems.Thm_MultiUnitProphet_claim_2
-- name    : MultiUnitProphet.claim_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:13:19.622199+00:00
-- url     : https://prove2.me/theorems/101eef8a-c1c5-40ce-956b-3e8953135776
-- title:
--   Claim 2 — (Min-Revenue) has an optimum with $r_1=r_2$ or $r_i\in\{0,1\}$, unique and diagonal when $Q_2^2-Q_{\ge3}(Q_1-Q_2)>0$
-- statement:
--   Let $Q_1,Q_2,Q_{\ge3}\ge0$ and $\phi\in\mathbb R$, and suppose the (Min-Revenue) program
--
--   $$\max\ (Q_2+Q_{\ge3})(r_1+r_2)+Q_1r_1r_2\quad\text{s.t. } r_1,r_2\in[0,1],\ r_1r_2(Q_1-Q_2)+(r_1+r_2)Q_2=\phi-Q_{\ge3}$$
--
--   is feasible. Then:
--
--   1. some optimal solution satisfies $r_1=r_2$, or $r_1\in\{0,1\}$, or $r_2\in\{0,1\}$;
--   2. if $Q_2^2-Q_{\ge3}(Q_1-Q_2)>0$, the optimal solution is unique and satisfies $r_1=r_2$.
--
--   Lemma 5 applies this to two unequal non-degenerate biases of a minimizer.
--
--   Differences from the source:
--   - reading: there always exists an optimal solution → if the feasible set is nonempty, there is a maximizer with the stated property; reason: an infeasible program has no optimal solution; the paper's programs are feasible because they come from a feasible solution
--   - generalization: Q_1, Q_2, Q_{≥3} probabilities of X̄ and the constant φ⋆_k → any nonnegative reals Q_1, Q_2, Q_{≥3} and any real φ; reason: the paper's values are a special case
--   - encoding: optimal solution of a Maximize program → IsMaxOn of the objective on the feasible set; reason: same notion
-- source:
--   Chawla, Devanur & Lykouris, Static pricing for multi-unit prophet inequalities, arXiv:2007.07990v4, Claim 2, p.12 (proof p.14)

import Mathlib
import Definitions.Def_MultiUnitProphet_MinRevenue

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MultiUnitProphet

/-- **Claim 2: the (Min-Revenue) program has an optimum on the diagonal or on the boundary, and a
unique diagonal optimum when `Q_2² − Q_{≥3}(Q_1 − Q_2) > 0`.**
Chawla, Devanur & Lykouris, *Static pricing for multi-unit prophet inequalities*,
arXiv:2007.07990v4, Claim 2, p.12 (proof p.14): "There always exists an optimal solution for the
(Min-Revenue) program that satisfies r1 = r2, or r1 ∈ {0, 1}, or r2 ∈ {0, 1}. Moreover, when
(Q2)² − Q≥3(Q1 − Q2) > 0, the unique optimal solution satisfies r1 = r2."

For nonnegative `Q_1, Q_2, Q_{≥3}`, any constant `φ` and a feasible (Min-Revenue) program:
1. some maximizer has `r_1 = r_2` or `r_1 ∈ {0,1}` or `r_2 ∈ {0,1}`;
2. if `Q_2² − Q_{≥3}(Q_1 − Q_2) > 0`, the maximizer is unique and has `r_1 = r_2`.

**Formalization Note.** "There always exists an optimal solution" is read for a feasible program
(the paper's program is feasible: it comes from a feasible solution of (GenBern : min µ s.t. δ = φ)).
The `Q`'s are any nonnegative reals and `φ` any real (the paper's are probabilities and `φ⋆_k`). -/
theorem claim_2 (Q1 Q2 Q3 φ : ℝ) (hQ1 : 0 ≤ Q1) (hQ2 : 0 ≤ Q2) (hQ3 : 0 ≤ Q3)
    (hK : (minRevFeasible Q1 Q2 Q3 φ).Nonempty) :
    (∃ r ∈ minRevFeasible Q1 Q2 Q3 φ,
        IsMaxOn (minRevObj Q1 Q2 Q3) (minRevFeasible Q1 Q2 Q3 φ) r ∧
        (r.1 = r.2 ∨ r.1 = 0 ∨ r.1 = 1 ∨ r.2 = 0 ∨ r.2 = 1)) ∧
    (0 < Q2 ^ 2 - Q3 * (Q1 - Q2) →
      ∃ r ∈ minRevFeasible Q1 Q2 Q3 φ,
        IsMaxOn (minRevObj Q1 Q2 Q3) (minRevFeasible Q1 Q2 Q3 φ) r ∧ r.1 = r.2 ∧
        ∀ s ∈ minRevFeasible Q1 Q2 Q3 φ,
          IsMaxOn (minRevObj Q1 Q2 Q3) (minRevFeasible Q1 Q2 Q3 φ) s → s = r) := by sorry

end MultiUnitProphet
