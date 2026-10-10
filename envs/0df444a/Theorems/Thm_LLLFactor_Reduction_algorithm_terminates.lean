-- Prove2me | Theorems.Thm_LLLFactor_Reduction_algorithm_terminates
-- name    : LLLFactor.Reduction.algorithm_terminates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:36.168984+00:00
-- url     : https://prove2.me/theorems/2b0c8753-ad27-4b02-9324-8641deb11521
-- title:
--   (1.15), (1.23) — the basis reduction algorithm terminates and returns a reduced basis for L
-- statement:
--   Let $n\ge1$ and let $b_1,\dots,b_n$ be a basis of $\mathbb R^n$, spanning the lattice $L=\sum_i\mathbb Z b_i$. Run the basis reduction algorithm (1.15) from the state $(b,2)$. Then:
--
--   1. **the algorithm terminates:** there is no infinite sequence of states $s_0=(b,2),s_1,s_2,\dots$ in which each $s_{t+1}$ arises from $s_t$ by one step;
--   2. **it does not get stuck:** at every reachable state $(b',k)$ with $k\le n$ some step applies;
--   3. **its output is a reduced basis for $L$:** at every reachable state $(b',n+1)$, the vectors $b'_1,\dots,b'_n$ form a basis for $L$ that is reduced in the sense of (1.4)–(1.5).
--
--   In the paper's words: "(1.15) We shall now describe an algorithm that transforms a given basis $b_1,b_2,\dots,b_n$ for a lattice $L$ into a reduced one. … This finishes the description of the algorithm. Below we shall prove that the algorithm terminates." The proof is (1.23). Together with (1.6)–(1.12), which bound the vectors of a reduced basis, this theorem is what makes reduced bases computable and is the engine of the factoring algorithm of Sect. 3.
--
--   **Formalization Note.** Every choice the algorithm leaves open (the nearest integer at a tie) is quantified over, so the theorem covers every implementation of the text of (1.15). Item 2 rules out a vacuous reading of item 1.
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), pp. 518–522, (1.15) and (1.23)

import Mathlib
import Definitions.Def_LLLFactor_Reduction_Algorithm

namespace LLLFactor.Reduction

theorem algorithm_terminates {n : ℕ} (hn : 0 < n) (b : Fin n → LLLFactor.RedBasis.Vec n)
    (hb : LinearIndependent ℝ b) :
    (¬ ∃ s : ℕ → State n, s 0 = (b, 2) ∧ ∀ t, Step (s t) (s (t + 1))) ∧
    (∀ s : State n, Reachable b s → s.2 ≤ n → ∃ s' : State n, Step s s') ∧
    (∀ s : State n, Reachable b s → s.2 = n + 1 →
      LLLFactor.RedBasis.IsBasisFor s.1 (LLLFactor.RedBasis.latticeOf b) ∧ LLLFactor.RedBasis.IsReduced s.1) := by sorry

end LLLFactor.Reduction
