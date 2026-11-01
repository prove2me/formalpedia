-- Prove2me | Theorems.Thm_MultiIssueMediation_lemma_1
-- name    : MultiIssueMediation.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:20.093175+00:00
-- url     : https://prove2.me/theorems/6c1997f1-9e41-470d-8d0c-dcf023d15895
-- title:
--   Lemma 1 — value regions of an adjacent rule (corrected: one common $y\ne o_Y$ in clause (i))
-- statement:
--   Let $f$ be an adjacent rule, and let $a=b_k=f_{k,k}$ and $b=b_r=f_{r,r}$ be bundles of $\mathbf B$, with value regions $V(a)$, $V(b)$. Then:
--
--   1. $a$ never appears outside of $V(a)$;
--   2. if $a\ne b$, then $a$ and $b$ do not both appear in $V(a)\cap V(b)$;
--   3. if $a\ne b$ and both appear on the same column with $a$ above $b$, or both appear on the same row with $a$ on the left of $b$, then on the main diagonal $a$ appears above $b$, that is, $k<r$.
--
--   The lemma locates the bundles of an adjacent rule, and it is the structure used to prove that adjacent rules are strategy-proof.
--
--   Differences from the source:
--   - correction: clause (i): f_{ℓ,j} = (o_X, y) for some y ∈ Y, cell by cell → one y ≠ o_Y common to all cells with ℓ < j; reason: the printed clause is false in the if direction: for m = 2, f_{1,1} = b_1, f_{2,2} = b_2, f_{2,1} = b_1, f_{1,2} = (o_X, o_Y) satisfies it, yet (o_X, y_1) dominates f_{1,2} by monotonicity, so f is not efficient; the proof (Part i, p.31) and Theorem 3 (p.21) have the corrected form
--   - reading: there exists a precedence order, printed inside "If ℓ > j" → one strict total order on B, quantified outside all cells; reason: per-cell existence would make the display empty and the if direction false (m = 3, f_{2,1} = b_1, f_{3,2} = b_2, f_{3,1} = b_2); Example 2 (p.16) and Step 2 (pp.34–37) use one global order
--   - reading: "for any two bundles a, b ∈ B" → clauses (ii) and (iii) carry a ≠ b; reason: both clauses are false for a = b; the proof treats two distinct bundles
--   - reading: "a and b both never appear in V(a) ∩ V(b)" → a and b do not both appear in V(a) ∩ V(b); reason: the other reading, that neither appears there, is false: with b_k on top of ▷ and k < r, f_{r,k} = b_k lies in V(b_k) ∩ V(b_r)
--   - reading: a consistent extension map Λ; Definition 1 constrains it from one side and Theorem 1 does not name it → Λ(θ_i) is the set of all consistent orderings (admissibleOrderings); reason: it is the only reading under which Theorem 1 is true (singleton maps give a counterexample at m = 3) and the one the proof uses, pp.28–29
--   - reading: there exists a one-to-one mapping t_i : X → Y → the fixed map t(x_k) = y_{m+1−k}, t(o_X) = o_Y, for both negotiators; reason: Example 1 (pp.13–14) and the definition of B (p.14) fix it; t(o_X) is never used
--   - encoding: types in Θ_i, m+1 positions of o_X → the m rows and m columns of the paper's matrix, indexed by Fin m; reason: the paper's own domain M × M (p.15), which leaves out the type that accepts nothing
--   - encoding: indices 1, …, m, outside options o_X, o_Y, cells f_{ℓ−1,j}, f_{ℓ,j+1} → Fin m with value = index − 1, Option (Fin m) with none the outside option, Fin.rev for m+1−k, indices p, q with p + 1 = ℓ, q = j + 1; reason: Lean conventions; the instances are the same
-- source:
--   Kesten, Özyurt, Efficient and Incentive Compatible Mediation: An Ordinal Market Design Approach, working paper, 4 October 2018, Lemma 1, pp.29–30

import Mathlib
import Definitions.Def_MultiIssueMediation_RuleGeometry

namespace MultiIssueMediation

/-- **Lemma 1** (Kesten, Özyurt, *Efficient and Incentive Compatible Mediation: An Ordinal Market
Design Approach*, working paper, 4 October 2018, Lemma 1, pp.29–30). For an adjacent rule, write
`a = b_k = f_{k,k}` and `b = b_r = f_{r,r}`:
(i) `a` never appears outside of its value region `V(a)`;
(ii) for `a ≠ b`, `a` and `b` do not both appear in `V(a) ∩ V(b)`;
(iii) for `a ≠ b`, if `a` and `b` appear on the same column with `a` above `b`, or on the same row
with `a` on the left of `b`, then `a` appears above `b` on the main diagonal, that is `k < r`.

**Formalization Note.** A bundle of `B` is `logrollBundle k`, which is `f_{k,k}` by clause (ii) of
the rule. "Above" is a smaller row index and "on the left" is a smaller column index (p.29). -/
theorem lemma_1 {m : ℕ} (hm : 2 ≤ m) (f : MediationRule m) (hf : IsAdjacentRule f) :
    (∀ k ℓ j : Fin m, f ℓ j = logrollBundle k → (ℓ, j) ∈ valueRegion k) ∧
      (∀ k r : Fin m, k ≠ r →
        ¬ ((∃ c ∈ valueRegion k ∩ valueRegion r, f c.1 c.2 = logrollBundle k) ∧
          (∃ c ∈ valueRegion k ∩ valueRegion r, f c.1 c.2 = logrollBundle r))) ∧
      (∀ k r j ℓ ℓ' : Fin m, k ≠ r → ℓ < ℓ' →
        f ℓ j = logrollBundle k → f ℓ' j = logrollBundle r → k < r) ∧
      (∀ k r ℓ j j' : Fin m, k ≠ r → j < j' →
        f ℓ j = logrollBundle k → f ℓ j' = logrollBundle r → k < r) := by sorry

end MultiIssueMediation
