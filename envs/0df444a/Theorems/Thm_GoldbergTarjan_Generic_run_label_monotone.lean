-- Prove2me | Theorems.Thm_GoldbergTarjan_Generic_run_label_monotone
-- name    : GoldbergTarjan.Generic.run_label_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:27:48.511573+00:00
-- url     : https://prove2.me/theorems/ba4ec264-f4f8-485c-aac0-f7bacebb2de0
-- title:
--   Lemma 3.6 — distance labels never decrease, and a relabeling increases the label
-- statement:
--   Let $(f_0,d_0), \dots, (f_K,d_K)$ be an execution of the generic algorithm on a flow network, started from the initial state of Fig. 2 with the simple labeling. Then:
--
--   1. for every vertex $v$ and all $k \le l \le K$, $d_k(v) \le d_l(v)$ (the label of $v$ never decreases);
--   2. if the step from $k$ to $k+1$ ($k < K$) is a relabeling of $v$, then $d_k(v) < d_{k+1}(v)$:
--   $$\text{Relabel}(v) \text{ at step } k \ \Longrightarrow\ d_{k+1}(v) > d_k(v).$$
--
--   Monotonicity of labels is what makes labels a potential for the counting arguments of Lemmas 3.8–3.10.
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, p. 927, Lemma 3.6

import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Run

namespace GoldbergTarjan.Generic

/-- Lemma 3.6 (Goldberg–Tarjan 1988, p. 927). For any vertex `v`, the distance label `d(v)`
never decreases along an execution of the generic algorithm, and an application of a
relabeling operation to `v` increases `d(v)` strictly. -/
theorem run_label_monotone {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (σ : ℕ → State V) (K : ℕ) (hrun : IsRun N σ K) :
    (∀ (v : V) (k l : ℕ), k ≤ l → l ≤ K → (σ k).2 v ≤ (σ l).2 v) ∧
      (∀ (v : V) (k : ℕ), k < K → RelabelStep N (σ k) (σ (k + 1)) v →
        (σ k).2 v < (σ (k + 1)).2 v) := by sorry

end GoldbergTarjan.Generic
