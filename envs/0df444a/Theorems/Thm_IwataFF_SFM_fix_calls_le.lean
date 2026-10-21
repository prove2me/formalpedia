-- Prove2me | Theorems.Thm_IwataFF_SFM_fix_calls_le
-- name    : IwataFF.SFM.fix_calls_le
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:42:12.714214+00:00
-- url     : https://prove2.me/theorems/7101f158-9d3a-4947-98ee-9149efdd8e27
-- title:
--   Proof of Theorem 4.2, p. 13 — Fix is called at most $n^2$ times
-- statement:
--   Let $n \ge 1$ and $f$ a real submodular function on the subsets of $\{0, \dots, n-1\}$ with $f(\emptyset) = 0$. Along every run of the algorithm of Figure 3 on $f$, the number of calls of the procedure Fix is at most
--   $$n^2.$$
--
--   Each call ends with a new arc of $D$ (possibly followed by a contraction) or a deletion of vertices, and this can happen at most $n^2$ times.
-- source:
--   Iwata, Fleischer & Fujishige, A Combinatorial, Strongly Polynomial-Time Algorithm for Minimizing Submodular Functions, arXiv:math/0004089v1, p. 13, proof of Theorem 4.2

import Mathlib
import Definitions.Def_IwataFF_SFM_Basic
import Definitions.Def_IwataFF_SFM_Phase
import Definitions.Def_IwataFF_SFM_Main

namespace IwataFF.SFM

/-- Proof of Theorem 4.2, p. 13 (arXiv:math/0004089v1): along every run of Figure 3 on a ground
set of `n` elements, `Fix` is called at most `n²` times. -/
theorem fix_calls_le {n : ℕ} (hn : 1 ≤ n) (f : Finset (Fin n) → ℝ)
    (hsub : SubmodularOn Finset.univ f) (hf0 : f ∅ = 0)
    (s : ℕ → MainState n) (k : ℕ) (hrun : IsRun f s k) :
    callCount s k ≤ n ^ 2 := by sorry

end IwataFF.SFM
