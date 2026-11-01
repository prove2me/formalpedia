-- Prove2me | Theorems.Thm_MultiIssueMediation_lemma_3
-- name    : MultiIssueMediation.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:12.371818+00:00
-- url     : https://prove2.me/theorems/6ed8b93f-2d8d-4b48-9b78-79496e1e7d12
-- title:
--   Lemma 3 — adjacency
-- statement:
--   Let $f$ be efficient, individually rational and strategy-proof, $m\ge 2$. For all $m\ge\ell>j$,
--
--   $$f_{\ell,j}\in\{f_{\ell-1,j},f_{\ell,j+1}\}\subset\mathbf B.$$
--
--   This is the first half of clause (iii) of Theorem 1: a bundle below the main diagonal equals the bundle immediately above it or immediately to its right.
--
--   Differences from the source:
--   - reading: a consistent extension map Λ; Definition 1 constrains it from one side and Theorem 1 does not name it → Λ(θ_i) is the set of all consistent orderings (admissibleOrderings); reason: it is the only reading under which Theorem 1 is true (singleton maps give a counterexample at m = 3) and the one the proof uses, pp.28–29
--   - reading: there exists a one-to-one mapping t_i : X → Y → the fixed map t(x_k) = y_{m+1−k}, t(o_X) = o_Y, for both negotiators; reason: Example 1 (pp.13–14) and the definition of B (p.14) fix it; t(o_X) is never used
--   - encoding: types in Θ_i, m+1 positions of o_X → the m rows and m columns of the paper's matrix, indexed by Fin m; reason: the paper's own domain M × M (p.15), which leaves out the type that accepts nothing
--   - encoding: indices 1, …, m, outside options o_X, o_Y, cells f_{ℓ−1,j}, f_{ℓ,j+1} → Fin m with value = index − 1, Option (Fin m) with none the outside option, Fin.rev for m+1−k, indices p, q with p + 1 = ℓ, q = j + 1; reason: Lean conventions; the instances are the same
-- source:
--   Kesten, Özyurt, Efficient and Incentive Compatible Mediation: An Ordinal Market Design Approach, working paper, 4 October 2018, Lemma 3, p.33

import Mathlib
import Definitions.Def_MultiIssueMediation_RuleGeometry

namespace MultiIssueMediation

/-- **Lemma 3** (Kesten, Özyurt, *Efficient and Incentive Compatible Mediation: An Ordinal Market
Design Approach*, working paper, 4 October 2018, Lemma 3, p.33): for an efficient, individually
rational and strategy-proof rule, for all `m ≥ ℓ > j`, `f_{ℓ,j} ∈ {f_{ℓ−1,j}, f_{ℓ,j+1}} ⊂ B`. -/
theorem lemma_3 {m : ℕ} (hm : 2 ≤ m) (f : MediationRule m) (hE : Efficient f)
    (hIR : IndividuallyRational f) (hSP : StrategyProof f) (ℓ j p q : Fin m) (hjℓ : j < ℓ)
    (hp : p.val + 1 = ℓ.val) (hq : q.val = j.val + 1) : AdjacentCell f ℓ j p q := by sorry

end MultiIssueMediation
