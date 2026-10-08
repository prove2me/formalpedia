-- Prove2me | Theorems.Thm_LLLFactor_Reduction_case2_count_le
-- name    : LLLFactor.Reduction.case2_count_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:42.509533+00:00
-- url     : https://prove2.me/theorems/69d8c486-0e89-49f7-b484-5bf34b094a86
-- title:
--   (1.23), p. 522 — along any run from k = 2, case 2 is passed at most n − 1 more times than case 1
-- statement:
--   Let $n\ge1$ and $b_1,\dots,b_n\in\mathbb R^n$. Let $s_0,s_1,\dots,s_T$ be a run of the algorithm (1.15) started at $s_0=(b,2)$, i.e. each $s_{t+1}$ arises from $s_t$ by one step, for $t<T$. Let $c_1$ and $c_2$ be the numbers of $t<T$ at which the step is of case 1, resp. case 2. Then
--   $$c_2\ \le\ c_1+(n-1).$$
--
--   This is the counting argument of (1.23): case 1 lowers $k$ by $1$, case 2 raises it by $1$, $k$ starts at $2$ and never exceeds $n+1$. Combined with the bound on the number of case-1 steps, it bounds the length of every run.
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), p. 522, (1.23)

import Mathlib
import Definitions.Def_LLLFactor_Reduction_Algorithm

namespace LLLFactor.Reduction

open Classical in
theorem case2_count_le {n : ℕ} (hn : 0 < n) (b : Fin n → LLLFactor.RedBasis.Vec n)
    (s : ℕ → State n) (T : ℕ) (hs0 : s 0 = (b, 2))
    (hrun : ∀ t < T, Step (s t) (s (t + 1))) :
    ((Finset.range T).filter (fun t => Case2 (s t) (s (t + 1)))).card ≤
      ((Finset.range T).filter (fun t => Case1 (s t) (s (t + 1)))).card + (n - 1) := by sorry

end LLLFactor.Reduction
