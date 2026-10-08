-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_clbi_propagation
-- name    : NestedSeatAlloc.IntPolicy.clbi_propagation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:39:31.177341+00:00
-- url     : https://prove2.me/theorems/a06392e6-1515-4d84-a770-071dcb2ec815
-- title:
--   Proof of Theorem 2, p. 133 — ER_k CLBI and integer p*₁, …, p*_k satisfying (20) make ER_{k+1}[s; p*; X] CLBI
-- statement:
--   Work in the seat model with integer-valued demands $X_1, X_2, \dots$. Let $p^* = (p^*_1, p^*_2, \dots)$ be a policy with integer protection levels $p^*_j \in \{0, 1, 2, \dots\}$, and fix $k \ge 1$. Suppose that
--
--   1. $s \mapsto ER_k[s; p^*; X]$ is CLBI on $s \ge 0$, and
--   2. $p^*_1, \dots, p^*_k$ satisfy (20):
--   $$f_{j+1} \in \delta ER_j[p^*_j; (p_0, \dots, p^*_{j-1}); X], \qquad j = 1, \dots, k.$$
--
--   Then $s \mapsto ER_{k+1}[s; p^*; X]$ is CLBI on $s \ge 0$.
--
--   This is the induction step of the proof of Theorem 2: together with the covering property it produces the next integer protection level $p^*_{k+1}$.
--
--   **Formalization Note** The integer policy is a sequence of natural numbers, used as real protection levels. CLBI means concave on $s \ge 0$ and affine on each $[m, m+1]$, $m \in \mathbb N$.
-- source:
--   Brumelle & McGill (1993), Operations Research 41(1), proof of Theorem 2, p. 133, left column ("Now suppose that ER_k[s; p; x] is CLBI …")

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

/-- CLBI propagation, proof of Theorem 2, p. 133: with integer-valued demand, if `ER_k[s; p*; X]` is CLBI on
`s ≥ 0` and the integer protection levels `p*_1, …, p*_k` satisfy (20), then `ER_{k+1}[s; p*; X]` is CLBI. -/
theorem clbi_propagation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hint : ∀ k ω, ∃ n : ℕ, X k ω = n) (k : ℕ) (hk : 1 ≤ k) (p : ℕ → ℕ)
    (hclbi : IsCLBI (expRevenue P X f (fun j => (p j : ℝ)) k))
    (h20 : ∀ j ∈ Finset.Icc 1 k,
      InSubdiff (expRevenue P X f (fun j => (p j : ℝ)) j) (p j) (f (j + 1))) :
    IsCLBI (expRevenue P X f (fun j => (p j : ℝ)) (k + 1)) := by sorry

end NestedSeatAlloc.IntPolicy
