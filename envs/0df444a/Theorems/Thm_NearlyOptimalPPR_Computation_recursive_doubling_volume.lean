-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_doubling_volume
-- name    : NearlyOptimalPPR.Computation.recursive_doubling_volume
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:05:13.901547+00:00
-- url     : https://prove2.me/theorems/44175082-f7aa-4235-8d8d-a3ea4f71ff16
-- title:
--   Weighted count of potential-doubling full solves
-- statement:
--   Fix increasing full-solve times $\tau(0)<\cdots<\tau(T)$ for a level $j$ that remains open throughout their interval. At each time before the final snapshot the solve is permitted, the computation is running, and no open budget is exhausted. Let $D_i$ consist of vertices whose level-$j$ potential more than doubles in the full solve at $\tau(i)$, and let $F=H_j(\tau(T))$. If the root active region still omits a vertex reachable from the seed at the final snapshot, then
--
--   $$\sum_{i<T}\operatorname{vol}(D_i)\le
--   \operatorname{vol}(F)\,
--   \frac{\log(3/q)-\log(3q/8)}{\log2}.$$
--
--   The root threshold satisfies $0<q\le1$, the teleportation parameter satisfies $0<\alpha\le1/2$, and the seed is nonisolated. All snapshots are finite reachable prefixes.
--
--   This weighted doubling bound combines the activation floor with the potential cap from Lemma 3.7. It controls the exceptional full solves in the proof of Lemma 4.4.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Lemmas 5.7–5.8 and their proof pp.26–28; Lemma 4.4 p.18 and finite-prefix counts pp.28–29.

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
open Finset Matrix NearlyOptimalPPR.Computation

theorem NearlyOptimalPPR.Computation.recursive_doubling_volume (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α ≤ 1/2) (hq : 0 < q ∧ q ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (τ : ℕ → ℕ) (hτ : StrictMono τ) (T j : ℕ) :
    let run := recursiveRun m g s α q ℓ schedule
    let F := ((run (τ T)).frames j).active
    (∀ t, τ 0 ≤ t → t ≤ τ T → j ≤ (run t).top) →
    (∀ k < T, (run (τ k)).top = j ∧ (run (τ k)).done = false ∧
      ¬componentComplete (run (τ k)) ∧ ((run (τ k)).frames j).pc = .fullSolve ∧
      ¬anyExhausted (run (τ k))) →
    (∃ v, g.graph.Reachable s v ∧ v ∉ ((run (τ T)).frames 0).active) →
    (∑ k ∈ Finset.range T, (volumeNat g (fullSolveDoubles g α (run (τ k)) j) : ℝ)) ≤
      (volumeNat g F : ℝ)*((Real.log (3/q)-Real.log (3*q/8))/Real.log 2) := by sorry
