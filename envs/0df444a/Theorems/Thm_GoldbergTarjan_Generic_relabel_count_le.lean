-- Prove2me | Theorems.Thm_GoldbergTarjan_Generic_relabel_count_le
-- name    : GoldbergTarjan.Generic.relabel_count_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:29:40.3402+00:00
-- url     : https://prove2.me/theorems/0dfbd779-eb00-46ad-8c49-4e25773412fc
-- title:
--   Lemma 3.8 — at most $2n-1$ relabelings per vertex and at most $(2n-1)(n-2) < 2n^2$ overall
-- statement:
--   Let $N$ be a flow network with $n$ vertices and let $(f_0,d_0), \dots, (f_K,d_K)$ be an execution of the generic algorithm, started from the initial state of Fig. 2 with the simple labeling. Then
--
--   1. every vertex $v$ is relabeled at most $2n - 1$ times among the $K$ steps;
--   2. the total number of relabeling steps is at most $(2n-1)(n-2)$;
--   3. $(2n-1)(n-2) < 2n^2$.
--
--   $$\#\{\text{relabelings}\} \le (2n-1)(n-2) < 2n^2.$$
--
--   This is the first of the three counts whose sum bounds the number of basic operations in Theorem 3.11.
--
--   **Formalization Note.** The subtractions $2n-1$ and $n-2$ are natural-number subtractions; they are exact because $s \ne t$ forces $n \ge 2$.
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, p. 927, Lemma 3.8

import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Run

namespace GoldbergTarjan.Generic

/-- Lemma 3.8 (Goldberg–Tarjan 1988, p. 927). The number of relabeling operations is at most
`2n - 1` per vertex and at most `(2n - 1)(n - 2) < 2n²` overall, where `n = |V|`. -/
theorem relabel_count_le {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (σ : ℕ → State V) (K : ℕ) (hrun : IsRun N σ K) :
    (∀ v : V, relabelCountAt N σ K v ≤ 2 * Fintype.card V - 1) ∧
      relabelCount N σ K ≤ (2 * Fintype.card V - 1) * (Fintype.card V - 2) ∧
      (2 * Fintype.card V - 1) * (Fintype.card V - 2) < 2 * Fintype.card V ^ 2 := by sorry

end GoldbergTarjan.Generic
