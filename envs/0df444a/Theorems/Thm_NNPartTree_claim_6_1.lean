-- Prove2me | Theorems.Thm_NNPartTree_claim_6_1
-- name    : NNPartTree.claim_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:10:53.013654+00:00
-- url     : https://prove2.me/theorems/d985cc44-8afb-403a-a1d8-3f6a864c856b
-- title:
--   Claim 6.1, p.22 — scanning $\lceil 4n\,\mathrm{cost}_{\mathcal D}(T)/\delta^2\rceil$ points bottom-up finds a nearest neighbor with probability $1-\delta$
-- statement:
--   Let $P$ be injective, $\mathcal D$ a nearest neighbor distribution, $T$ a cut tree, and $\delta\in(0,1)$. Let the scan order of a query $q$ list the points of mass at least $\delta/(2n)$, once each, in the bottom-up order of $T$ from the leaf of $q$, with any tie-breaking. Then, except with probability at most $\delta$ over $(q,p^\star)\sim\mathcal D$, the point $p^\star$ is among the first $\lceil 4n\,\mathrm{cost}_{\mathcal D}(T)/\delta^2\rceil$ scanned points, and any closest scanned point is a nearest neighbor of $q$. The route of $q$ evaluates at most $\mathrm{depth}(T)$ cuts.
--
--   So a low-cost tree of low-complexity cuts yields a fast nearest neighbor search.
--
--   Differences from the source:
--   - generalization: T β-balanced of complexity τ; q ∼ D_q with p★ = NN(q) → any cut tree; any nearest neighbor pair distribution; reason: the correctness proof does not use balance, and the induced case of §6 is an instance
--   - encoding: runs in time O(τ d_T) + O(nd/δ² · cost_D(T)) → at most depth(T) cut evaluations and at most ⌈4n cost_D(T)/δ²⌉ scanned points; reason: time is τ × (count) + d × (count); depth d_T is the printed term
--   - encoding: there exists an algorithm that returns NN(q) → the proof's algorithm, for every tie-breaking of the scan; a closest scanned point is a nearest neighbor; reason: under a tie NN(q) is not unique; failure set bounded in outer measure
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Claim 6.1, p.22; proof pp.22–23

import Mathlib
import Definitions.Def_NNPartTree_CutTree

open MeasureTheory

namespace NNPartTree

/-- **Claim 6.1**, p.22; proof pp.22–23. S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…).

Let `T` be a cut tree, `δ ∈ (0, 1)`. The algorithm routes `q` down `T` and scans the first `⌈4n cost_D(T)/δ²⌉` points of the bottom-up order
over points of mass at least `δ/(2n)`, returning the closest. Outside probability `δ` over `(q, p★) ∼ D`, `p★` is among the scanned points, and a
closest scanned point is a nearest neighbor of `q`.

**Formalization Note.** Time `O(τ d_T) + O(nd/δ² · cost_D(T))` is given as counts: at most `depth T` cut evaluations of cost `τ` and at most
`⌈4n cost_D(T)/δ²⌉` scanned points of cost `d`. The result holds for every tie-breaking of the scan order. Balance is not used for correctness and
the printed depth is what enters the time, so the hypothesis that `T` is `β`-balanced is dropped. -/
theorem claim_6_1 {n d : ℕ} (P : Fin n → Pt d) (hP : Function.Injective P)
    (D : Measure (Pt d × Pt d)) [IsProbabilityMeasure D] (hD : IsNNDist P D) (T : CutTree d)
    (hT : T.IsCutTree) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (ord : Pt d → List (Fin n))
    (hord : ∀ q, IsBottomUpScan P D δ T q (ord q)) :
    (∀ q, (T.addr q).length ≤ T.depth) ∧
    D {z | ¬ ((∃ i ∈ (ord z.1).take ⌈4 * n * (cost D T).toReal / δ ^ 2⌉₊, P i = z.2) ∧
        ∀ i ∈ (ord z.1).take ⌈4 * n * (cost D T).toReal / δ ^ 2⌉₊,
          (∀ i' ∈ (ord z.1).take ⌈4 * n * (cost D T).toReal / δ ^ 2⌉₊,
            ‖z.1 - P i‖ ≤ ‖z.1 - P i'‖) → ∀ j, ‖z.1 - P i‖ ≤ ‖z.1 - P j‖)} ≤
      ENNReal.ofReal δ := by sorry

end NNPartTree
