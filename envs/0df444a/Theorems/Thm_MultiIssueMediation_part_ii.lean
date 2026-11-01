-- Prove2me | Theorems.Thm_MultiIssueMediation_part_ii
-- name    : MultiIssueMediation.part_ii
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:19:38.920076+00:00
-- url     : https://prove2.me/theorems/1ed63f5e-603b-419c-aa49-68d432385a65
-- title:
--   Proof of Theorem 1, Part ii, pp.31–32 — the main diagonal is $\mathbf B$
-- statement:
--   Let $f$ be efficient, individually rational and strategy-proof, $m\ge 2$. For every $k$,
--
--   $$f_{k,k}=(x_k,y_{m+1-k}).$$
--
--   This is clause (ii) of Theorem 1: at the profiles with exactly one mutually acceptable alternative $x_k$, the rule gives the logrolling bundle of $x_k$.
--
--   Differences from the source:
--   - reading: a consistent extension map Λ; Definition 1 constrains it from one side and Theorem 1 does not name it → Λ(θ_i) is the set of all consistent orderings (admissibleOrderings); reason: it is the only reading under which Theorem 1 is true (singleton maps give a counterexample at m = 3) and the one the proof uses, pp.28–29
--   - reading: there exists a one-to-one mapping t_i : X → Y → the fixed map t(x_k) = y_{m+1−k}, t(o_X) = o_Y, for both negotiators; reason: Example 1 (pp.13–14) and the definition of B (p.14) fix it; t(o_X) is never used
--   - encoding: types in Θ_i, m+1 positions of o_X → the m rows and m columns of the paper's matrix, indexed by Fin m; reason: the paper's own domain M × M (p.15), which leaves out the type that accepts nothing
--   - encoding: indices 1, …, m, outside options o_X, o_Y, cells f_{ℓ−1,j}, f_{ℓ,j+1} → Fin m with value = index − 1, Option (Fin m) with none the outside option, Fin.rev for m+1−k, indices p, q with p + 1 = ℓ, q = j + 1; reason: Lean conventions; the instances are the same
-- source:
--   Kesten, Özyurt, Efficient and Incentive Compatible Mediation: An Ordinal Market Design Approach, working paper, 4 October 2018, proof of Theorem 1, Part ii, pp.31–32

import Mathlib
import Definitions.Def_MultiIssueMediation_MediationRule

namespace MultiIssueMediation

/-- **Part ii** of the 'only if' direction of Theorem 1 (Kesten, Özyurt, *Efficient and Incentive
Compatible Mediation: An Ordinal Market Design Approach*, working paper, 4 October 2018, proof of
Theorem 1, Part ii, pp.31–32): for an efficient, individually rational and strategy-proof rule,
`f_{k,k} = (x_k, y_{m+1−k})` for every `k`. -/
theorem part_ii {m : ℕ} (hm : 2 ≤ m) (f : MediationRule m) (hE : Efficient f)
    (hIR : IndividuallyRational f) (hSP : StrategyProof f) (k : Fin m) :
    f k k = logrollBundle k := by sorry

end MultiIssueMediation
