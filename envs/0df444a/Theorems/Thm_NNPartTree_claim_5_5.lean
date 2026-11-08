-- Prove2me | Theorems.Thm_NNPartTree_claim_5_5
-- name    : NNPartTree.claim_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:09:17.059929+00:00
-- url     : https://prove2.me/theorems/9b455ed5-d181-4277-bb3b-eb316b9e0e40
-- title:
--   Claim 5.5, p.17 — a feasible $A^\star$ for $\Pi(\mathcal D,C)$ gives a feasible $A$ for $\Pi(S,500C)$ of objective $\le 45\eta$ with probability $0.9$
-- statement:
--   Let $C>1$, and let $A^\star$ of degree at most $k$ be feasible for $\Pi(\mathcal D,C)$ with objective value $\eta=\mathbf E_{\mathcal D}[(A^\star(x)-A^\star(y))^2]$. If $m\ge 4000C$, then with probability at least $0.9$ over $S\sim\mathcal D^m$ there is a polynomial $A$ of degree at most $k$ feasible for $\Pi(S,500C)$ with objective value at most $45\eta$.
--
--   This transfers the population polynomial of Lemma 5.4 to the sample, where the semidefinite program is solved.
--
--   Differences from the source:
--   - generalization: A★ an optimal solution → A★ any feasible solution; reason: the proof uses only feasibility; an optimal solution is feasible
--   - encoding: O(η) → 45η; reason: the constant of the proof, p.18
--   - encoding: objective value η, with probability 0.9 → η a real number (finite moments are part of `PiFeasible`); failure set has outer measure at most 1/10; reason: η is a number as printed; the event quantifies over polynomials, and no measurability is claimed
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Claim 5.5, p.17; proof pp.17–18, constant p.18

import Mathlib
import Definitions.Def_NNPartTree_Moments

open MeasureTheory

namespace NNPartTree

/-- **Claim 5.5**, p.17; proof pp.17–18. S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…).

If `A★` is feasible for `Π(D, C)` with objective value `η` and `m ≥ 4000 C`, then with probability `0.9` over
`S ∼ D^m` there is a feasible `A` for `Π(S, 500 C)` of objective at most `45 η`. The constant `45` is the
proof's (p.18).

**Formalization Note.** The page takes `A★` optimal; the proof uses only feasibility. The failure set is
bounded in outer measure. `A` has degree at most `k`, as `A★` does (Definition 5.4). -/
theorem claim_5_5 {d : ℕ} (D : Measure (Pt d × Pt d)) [IsProbabilityMeasure D] (k : ℕ) (C : ℝ)
    (hC : 1 < C) (Astar : MvPolynomial (Fin d) ℝ) (hdeg : Astar.totalDegree ≤ k)
    (hfeas : PiFeasible D C Astar) (m : ℕ) (hm : 4000 * C ≤ m) :
    sampleProduct D m {S | ¬ ∃ A : MvPolynomial (Fin d) ℝ, A.totalDegree ≤ k ∧
        PiFeasible (empirical S) (500 * C) A ∧
        pairEnergy (empirical S) (peval A) ≤ 45 * pairEnergy D (peval Astar)} ≤
      ENNReal.ofReal (1 / 10) := by sorry

end NNPartTree
