-- Prove2me | Theorems.Thm_LinearPathTuran_Exact_theorem_4_5
-- name    : LinearPathTuran.Exact.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:23:56.747491+00:00
-- url     : https://prove2.me/theorems/0ac173c9-16ec-4c75-8e01-ce246390a412
-- title:
--   Theorem 4.5 — ex_k(n, ℙ_{2t+1}) ≤ ex_k(n, ℙ_{2t+2}) ≤ t·C(n−1, k−1) + O(n^{k−2})
-- statement:
--   Let $k\ge 4$ and $t\ge 1$. There is a constant $C$, depending only on $k$ and $t$, such that for every $n$
--   $$\mathbf{ex}_k(n,\mathbb P^{(k)}_{2t+1})\le\mathbf{ex}_k(n,\mathbb P^{(k)}_{2t+2})\le t\binom{n-1}{k-1}+C\,n^{k-2}.$$
--
--   This is the asymptotically tight upper bound; §5 sharpens it to the exact value of Theorem 2.4.
--
--   **Formalization Note** The paper's $O(n^{k-2})$ is an explicit constant $C$ chosen after $k,t$ and before $n$, valid for every $n$ (small $n$ are absorbed into $C$).
-- source:
--   Füredi, Jiang and Seiver, Exact solution of the hypergraph Turán problem for k-uniform linear paths, arXiv:1108.1247v1, p. 8, Theorem 4.5

import Mathlib
import Definitions.Def_LinearPathTuran_Exact_Setting

namespace LinearPathTuran.Exact

open Finset

/-- Theorem 4.5, p. 8: `ex_k(n, ℙ_{2t+1}) ≤ ex_k(n, ℙ_{2t+2}) ≤ t C(n-1, k-1) + O(n^{k-2})`. -/
theorem theorem_4_5 (k t : ℕ) (hk : 4 ≤ k) (ht : 1 ≤ t) :
    ∃ C : ℝ, ∀ n : ℕ, exLin n k (2 * t + 1) ≤ exLin n k (2 * t + 2) ∧
      (exLin n k (2 * t + 2) : ℝ) ≤
        t * ((n - 1).choose (k - 1) : ℝ) + C * (n : ℝ) ^ (k - 2) := by sorry

end LinearPathTuran.Exact
