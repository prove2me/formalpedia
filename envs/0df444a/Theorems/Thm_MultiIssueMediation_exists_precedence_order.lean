-- Prove2me | Theorems.Thm_MultiIssueMediation_exists_precedence_order
-- name    : MultiIssueMediation.exists_precedence_order
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:16.573181+00:00
-- url     : https://prove2.me/theorems/c1ad883a-fcea-45b5-8fb6-235cf082b987
-- title:
--   Proof of Theorem 1, p.37 — extension of $\triangleright_f$ to a strict total order satisfying (iii) (corrected: $a\ne b$ in the construction of $\triangleright_f$)
-- statement:
--   Let $f$ be efficient, individually rational and strategy-proof, $m\ge 2$. There is a complete, transitive and strict order $\triangleright$ on $\mathbf B$ that contains the relation $\triangleright_f$ of Step 2 and satisfies clause (iii) of Theorem 1: for all $\ell>j$,
--
--   $$f_{\ell,j}=\begin{cases} f_{\ell-1,j} & \text{if } f_{\ell-1,j}\triangleright f_{\ell,j+1},\\ f_{\ell,j+1} & \text{otherwise.}\end{cases}$$
--
--   This completes the 'only if' direction of Theorem 1.
--
--   Differences from the source:
--   - correction: f_{ℓ−1,j} ▷ f_{ℓ,j+1} whenever f_{ℓ,j} = f_{ℓ−1,j}, and symmetrically (p.35) → the relation ▷_f holds only between distinct bundles a ≠ b; reason: as printed, equal neighbours give a ▷ a and Lemma 4 is false: m = 3, an adjacent rule with b_2 on top, cell (3,1); the proof of Lemma 4 speaks of diagonally adjacent, hence distinct, bundles
--   - reading: a consistent extension map Λ; Definition 1 constrains it from one side and Theorem 1 does not name it → Λ(θ_i) is the set of all consistent orderings (admissibleOrderings); reason: it is the only reading under which Theorem 1 is true (singleton maps give a counterexample at m = 3) and the one the proof uses, pp.28–29
--   - reading: there exists a one-to-one mapping t_i : X → Y → the fixed map t(x_k) = y_{m+1−k}, t(o_X) = o_Y, for both negotiators; reason: Example 1 (pp.13–14) and the definition of B (p.14) fix it; t(o_X) is never used
--   - encoding: types in Θ_i, m+1 positions of o_X → the m rows and m columns of the paper's matrix, indexed by Fin m; reason: the paper's own domain M × M (p.15), which leaves out the type that accepts nothing
--   - encoding: indices 1, …, m, outside options o_X, o_Y, cells f_{ℓ−1,j}, f_{ℓ,j+1} → Fin m with value = index − 1, Option (Fin m) with none the outside option, Fin.rev for m+1−k, indices p, q with p + 1 = ℓ, q = j + 1; reason: Lean conventions; the instances are the same
-- source:
--   Kesten, Özyurt, Efficient and Incentive Compatible Mediation: An Ordinal Market Design Approach, working paper, 4 October 2018, proof of Theorem 1, p.37

import Mathlib
import Definitions.Def_MultiIssueMediation_RuleGeometry

namespace MultiIssueMediation

/-- **Final extension** (Kesten, Özyurt, *Efficient and Incentive Compatible Mediation: An Ordinal
Market Design Approach*, working paper, 4 October 2018, proof of Theorem 1, p.37): for an efficient,
individually rational and strategy-proof rule, there is a strict total order on `B` that contains
the relation `▷_f` of Step 2 and satisfies clause (iii) of Theorem 1. -/
theorem exists_precedence_order {m : ℕ} (hm : 2 ≤ m) (f : MediationRule m) (hE : Efficient f)
    (hIR : IndividuallyRational f) (hSP : StrategyProof f) :
    ∃ prec : logrollBundles m → logrollBundles m → Prop,
      IsStrictTotalOrder (logrollBundles m) prec ∧
        (∀ a b : logrollBundles m, derivedPrec f a b → prec a b) ∧
        AdjacencyClause f prec := by sorry

end MultiIssueMediation
