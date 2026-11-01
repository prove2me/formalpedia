-- Prove2me | Theorems.Thm_MultiIssueMediation_lemma_6
-- name    : MultiIssueMediation.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:46.204067+00:00
-- url     : https://prove2.me/theorems/d842f2db-2d92-4c99-af68-af472ac3276c
-- title:
--   Lemma 6 — $\triangleright_f$ has no 3-cycle (corrected: $a\ne b$ in the construction of $\triangleright_f$)
-- statement:
--   Let $f$ be efficient, individually rational and strategy-proof, $m\ge 2$, with $\triangleright_f$ the relation of Step 2. For any $a,b,c\in\mathbf B$ such that $a\triangleright_f b$ and $b\triangleright_f c$, we have not $c\triangleright_f a$.
--
--   The page calls this transitivity; as printed, and as stated here, it excludes 3-cycles only and does not assert $a\triangleright_f c$.
--
--   Differences from the source:
--   - correction: f_{ℓ−1,j} ▷ f_{ℓ,j+1} whenever f_{ℓ,j} = f_{ℓ−1,j}, and symmetrically (p.35) → the relation ▷_f holds only between distinct bundles a ≠ b; reason: as printed, equal neighbours give a ▷ a and Lemma 4 is false: m = 3, an adjacent rule with b_2 on top, cell (3,1); the proof of Lemma 4 speaks of diagonally adjacent, hence distinct, bundles
--   - reading: a consistent extension map Λ; Definition 1 constrains it from one side and Theorem 1 does not name it → Λ(θ_i) is the set of all consistent orderings (admissibleOrderings); reason: it is the only reading under which Theorem 1 is true (singleton maps give a counterexample at m = 3) and the one the proof uses, pp.28–29
--   - reading: there exists a one-to-one mapping t_i : X → Y → the fixed map t(x_k) = y_{m+1−k}, t(o_X) = o_Y, for both negotiators; reason: Example 1 (pp.13–14) and the definition of B (p.14) fix it; t(o_X) is never used
--   - encoding: types in Θ_i, m+1 positions of o_X → the m rows and m columns of the paper's matrix, indexed by Fin m; reason: the paper's own domain M × M (p.15), which leaves out the type that accepts nothing
--   - encoding: indices 1, …, m, outside options o_X, o_Y, cells f_{ℓ−1,j}, f_{ℓ,j+1} → Fin m with value = index − 1, Option (Fin m) with none the outside option, Fin.rev for m+1−k, indices p, q with p + 1 = ℓ, q = j + 1; reason: Lean conventions; the instances are the same
-- source:
--   Kesten, Özyurt, Efficient and Incentive Compatible Mediation: An Ordinal Market Design Approach, working paper, 4 October 2018, Lemma 6, p.36

import Mathlib
import Definitions.Def_MultiIssueMediation_RuleGeometry

namespace MultiIssueMediation

/-- **Lemma 6** (Kesten, Özyurt, *Efficient and Incentive Compatible Mediation: An Ordinal Market
Design Approach*, working paper, 4 October 2018, Lemma 6, p.36): for an efficient, individually
rational and strategy-proof rule, "for any triple `a, b, c ∈ B` such that `a ▷ b` and `b ▷ c`, we
have `¬ c ▷ a`", with `▷_f` the relation of Step 2.

**Formalization Note.** The page calls this transitivity. As printed, and as stated here, it
excludes 3-cycles only; it does not assert `a ▷_f c`. -/
theorem lemma_6 {m : ℕ} (hm : 2 ≤ m) (f : MediationRule m) (hE : Efficient f)
    (hIR : IndividuallyRational f) (hSP : StrategyProof f) (a b c : logrollBundles m)
    (hab : derivedPrec f a b) (hbc : derivedPrec f b c) : ¬ derivedPrec f c a := by sorry

end MultiIssueMediation
