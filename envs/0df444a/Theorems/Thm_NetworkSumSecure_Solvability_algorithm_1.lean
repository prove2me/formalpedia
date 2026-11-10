-- Prove2me | Theorems.Thm_NetworkSumSecure_Solvability_algorithm_1
-- name    : NetworkSumSecure.Solvability.algorithm_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T05:05:28.058811+00:00
-- url     : https://prove2.me/theorems/b14a1a6e-3349-4124-8019-13cb666aa343
-- title:
--   §6.1 equation (43) — Algorithm 1 constructs rank-valid causal local codes
-- statement:
--   Let $N$ be a finite network over a finite field $F$ with $|F|>|U|+1$, and fix $r+1$ edge-disjoint user-to-server paths $Q$. Put $z_i=\max(|Q_i|-1,0)$ and $I_Q=\{i:Q_i\ne\varnothing\}$. Specify an auxiliary user-to-server path $P_i$ for every $i\notin I_Q$, allowing overlap with other paths. Let $e_i$ be its last edge, and let $Q_\rho$ be the last edges of the $Q$ paths.
--
--   Algorithm 1 has an initialization and a complete legal finite execution. Every legal prefix shorter than the relay traversal admits one more legal step agreeing with all prior states. Every completed legal execution yields zero columns on unused original edges and satisfies
--
--   $$h_{e_i}^{(i)}\ne0\quad(i\notin I_Q),\qquad \operatorname{rank}(H_{Q_\rho}^{I_Q})=r+1.$$
--
--   Moreover, these columns are induced by causal local linear encoders with exactly the assignment $z$, and their server rank is at least $r+1$ with every user-block rank at least one. Thus the construction terminates after the prescribed finite traversal and produces the input required by Theorem 6.
--
--   **Formalization Note** The legal-choice relation specifies the initialization, moving frontier, incoming span and every exclusion in lines 12,14,16 independently of these output properties. No rank-validity premise or runtime assertion is included.
--
--   Differences from the source:
--   - encoding: Algorithm 1 processes the selected path union, with unused original edges set to zero → finite legal traces initialize source columns, traverse used relay edges in a topological order, and retain zero columns on unused original edges; reason: the independent trace relation records exactly the choices of lines 1–18 without building correctness into the definition
--   - encoding: the verification proves choices exist and preserves (43), hence (24) → existence of a complete trace, extension of every legal prefix, and local realizability plus full output correctness for every legal completion; reason: these clauses state the complete constructive result in (45)–(53) with the explicit sufficient condition q>s+1
--   - generalization: nonempty participant convention → empty user types are permitted in the surrounding types; reason: no family of r+1 user-starting paths can exist with no users, so no valid source construction is removed
-- source:
--   Yang Bai, Xuan Guang, Lizhi Wang, STOC 2027 submission #1291 (October 2026), p. 20 (PDF p. 22); setup p. 19 (PDF p. 21); Algorithm 1 p. 22 (PDF p. 24); verification pp. 21–24 (PDF pp. 23–26), §6.1 equation (43), Algorithm 1 and equations (39)–(53)

import Mathlib
import Definitions.Def_NetworkSumSecure_Solvability_algorithm

namespace NetworkSumSecure.Solvability

/-- §6.1, equation (43) and Algorithm 1, printed pp.20–24 (PDF 22–26).
Every legal prefix can continue, at least one finite execution exists, and every
legal completed execution is locally realizable and has the full stated output. -/
theorem algorithm_1 {V E U F : Type} [Fintype V] [Fintype E] [Fintype U]
    [Field F] [Fintype F] (N : Network V E U) (r : ℕ)
    (D : PathData N (r + 1)) (hq : Fintype.card U + 1 < Fintype.card F) :
    (∃ (O : EdgeOrder N) (I : Initialization D) (trace : ℕ → AlgorithmState D F),
      LegalPrefix O I (relayTraversal D O).length trace) ∧
    (∀ (O : EdgeOrder N) (I : Initialization D) (t : ℕ)
      (trace : ℕ → AlgorithmState D F), LegalPrefix O I t trace →
      t < (relayTraversal D O).length →
      ∃ trace' : ℕ → AlgorithmState D F,
        LegalPrefix O I (t + 1) trace' ∧ ∀ j, j ≤ t → trace' j = trace j) ∧
    (∀ (O : EdgeOrder N) (I : Initialization D) (trace : ℕ → AlgorithmState D F),
      LegalPrefix O I (relayTraversal D O).length trace →
      AlgorithmOutput D (trace (relayTraversal D O).length)) := by sorry

end NetworkSumSecure.Solvability
