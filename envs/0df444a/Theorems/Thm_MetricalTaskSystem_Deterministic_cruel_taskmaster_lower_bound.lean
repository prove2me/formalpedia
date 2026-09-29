-- Prove2me | Theorems.Thm_MetricalTaskSystem_Deterministic_cruel_taskmaster_lower_bound
-- name    : MetricalTaskSystem.Deterministic.cruel_taskmaster_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:12:37.162993+00:00
-- url     : https://prove2.me/theorems/7363b13e-7b66-4132-afcb-cc5ad442d9a1
-- title:
--   Theorem 2.2 — the cruel taskmaster forces $w_{\mathbf T(\varepsilon)}(A)\ge(2n-1)/(1+\varepsilon/\min_{i\ne j}d(i,j))$
-- statement:
--   Let $(S,d)$ be a metrical task system with $n\ge2$ states, let $A$ be any on-line algorithm, $s_0$ an initial state and $\varepsilon>0$. Let $\mathbf T(\varepsilon)$ be the infinite task sequence produced by the cruel taskmaster $M(\varepsilon)$ in response to $A$ (each task costs $\varepsilon$ in the state $A$ currently occupies and $0$ elsewhere). Then
--   $$w_{\mathbf T(\varepsilon)}(A)\ \ge\ \frac{2n-1}{1+\varepsilon/\min_{i\neq j}d(i,j)} .$$
--
--   Together with Lemma 2.1, letting $\varepsilon\to0$ gives $w(A)\ge 2n-1$ for every on-line algorithm, i.e. the lower bound in Theorem 1.1.
--
--   **Formalization Note** The hypothesis $n\ge2$ (`Nontrivial S`) is needed for $\min_{i\neq j}d(i,j)$ to be defined; at $n=1$ the paper's minimum ranges over the empty set.
-- source:
--   Borodin, Linial, Saks, An Optimal On-Line Algorithm for Metrical Task System, J. ACM 39(4) (1992), p. 749, Theorem 2.2 (strategy M(ε), p. 748)

import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model
import Definitions.Def_MetricalTaskSystem_Deterministic_CruelTaskmaster

namespace MetricalTaskSystem.Deterministic

/-- **Theorem 2.2** (Borodin–Linial–Saks 1992, p. 749). Let `A` be any on-line algorithm for a
metrical task system `(S, d)` with `n ≥ 2` states, and let `T(ε)` be the infinite task sequence
produced by the cruel taskmaster `M(ε)` in response to `A`. Then
`w_{T(ε)}(A) ≥ (2n − 1) / (1 + ε / min_{i ≠ j} d(i, j))`. -/
theorem cruel_taskmaster_lower_bound {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S]
    (d : S → S → ℝ) (hd : IsMetrical d) (A : OnlineAlgorithm S) (s₀ : S)
    (ε : ℝ) (hε : 0 < ε) :
    ((((2 * (Fintype.card S : ℝ) - 1) / (1 + ε / minOffDiag d)) : ℝ) : EReal) ≤
      ratioLimsup d A s₀ (cruelSeq A s₀ ε) := by sorry

end MetricalTaskSystem.Deterministic
