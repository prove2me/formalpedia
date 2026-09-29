-- Prove2me | Theorems.Thm_GoldbergTarjan_Generic_run_label_le
-- name    : GoldbergTarjan.Generic.run_label_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:28:17.580074+00:00
-- url     : https://prove2.me/theorems/bfc014c9-db9e-4b77-aa3e-29283d887af2
-- title:
--   Lemma 3.7 — every distance label stays at most $2n - 1$
-- statement:
--   Let $N$ be a flow network with $n$ vertices and let $(f_0,d_0), \dots, (f_K,d_K)$ be an execution of the generic algorithm, started from the initial state of Fig. 2 with the simple labeling. Then at any time and for any vertex,
--
--   $$d_k(v) \le 2n - 1 \qquad (0 \le k \le K,\ v \in V).$$
--
--   In particular all labels stay finite. This is the key amortization bound of the paper: it bounds the number of relabelings (Lemma 3.8) and, through them, the numbers of saturating and nonsaturating pushes.
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, p. 927, Lemma 3.7

import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Run

namespace GoldbergTarjan.Generic

/-- Lemma 3.7 (Goldberg–Tarjan 1988, p. 927). At any time during the execution of the
algorithm and for any vertex `v ∈ V`, `d(v) ≤ 2n - 1`, where `n = |V|`. -/
theorem run_label_le {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (σ : ℕ → State V) (K : ℕ) (hrun : IsRun N σ K) :
    ∀ k ≤ K, ∀ v : V, (σ k).2 v ≤ ((2 * Fintype.card V - 1 : ℕ) : ℕ∞) := by sorry

end GoldbergTarjan.Generic
