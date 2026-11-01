-- Prove2me | Theorems.Thm_MultiIssueMediation_lemma_4
-- name    : MultiIssueMediation.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:55.529143+00:00
-- url     : https://prove2.me/theorems/5106f2df-7bf0-4e18-beab-8fe3760e2bbe
-- title:
--   Lemma 4 — $\triangleright_f$ is asymmetric (corrected: $a\ne b$ in the construction of $\triangleright_f$)
-- statement:
--   Let $f$ be efficient, individually rational and strategy-proof, $m\ge 2$, and let $\triangleright_f$ be the relation constructed from the pairwise comparisons of Step 2. If $a\triangleright_f b$ for $a,b\in\mathbf B$, then not $b\triangleright_f a$.
--
--   Differences from the source:
--   - correction: f_{ℓ−1,j} ▷ f_{ℓ,j+1} whenever f_{ℓ,j} = f_{ℓ−1,j}, and symmetrically (p.35) → the relation ▷_f holds only between distinct bundles a ≠ b; reason: as printed, equal neighbours give a ▷ a and Lemma 4 is false: m = 3, an adjacent rule with b_2 on top, cell (3,1); the proof of Lemma 4 speaks of diagonally adjacent, hence distinct, bundles
--   - reading: a consistent extension map Λ; Definition 1 constrains it from one side and Theorem 1 does not name it → Λ(θ_i) is the set of all consistent orderings (admissibleOrderings); reason: it is the only reading under which Theorem 1 is true (singleton maps give a counterexample at m = 3) and the one the proof uses, pp.28–29
--   - reading: there exists a one-to-one mapping t_i : X → Y → the fixed map t(x_k) = y_{m+1−k}, t(o_X) = o_Y, for both negotiators; reason: Example 1 (pp.13–14) and the definition of B (p.14) fix it; t(o_X) is never used
--   - encoding: types in Θ_i, m+1 positions of o_X → the m rows and m columns of the paper's matrix, indexed by Fin m; reason: the paper's own domain M × M (p.15), which leaves out the type that accepts nothing
--   - encoding: indices 1, …, m, outside options o_X, o_Y, cells f_{ℓ−1,j}, f_{ℓ,j+1} → Fin m with value = index − 1, Option (Fin m) with none the outside option, Fin.rev for m+1−k, indices p, q with p + 1 = ℓ, q = j + 1; reason: Lean conventions; the instances are the same
-- source:
--   Kesten, Özyurt, Efficient and Incentive Compatible Mediation: An Ordinal Market Design Approach, working paper, 4 October 2018, Lemma 4, p.35, and Step 2, pp.34–35

import Mathlib
import Definitions.Def_MultiIssueMediation_RuleGeometry

namespace MultiIssueMediation

/-- **Lemma 4** (Kesten, Özyurt, *Efficient and Incentive Compatible Mediation: An Ordinal Market
Design Approach*, working paper, 4 October 2018, Lemma 4, p.35): for an efficient, individually
rational and strategy-proof rule, the relation `▷_f` of Step 2 is asymmetric. -/
theorem lemma_4 {m : ℕ} (hm : 2 ≤ m) (f : MediationRule m) (hE : Efficient f)
    (hIR : IndividuallyRational f) (hSP : StrategyProof f) (a b : logrollBundles m)
    (hab : derivedPrec f a b) : ¬ derivedPrec f b a := by sorry

end MultiIssueMediation
