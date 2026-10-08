-- Prove2me | Theorems.Thm_HassinRSP_Rounding_scaled_opt_error
-- name    : HassinRSP.Rounding.scaled_opt_error
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:28:01.965994+00:00
-- url     : https://prove2.me/theorems/2402090f-ffa7-4c1a-85c1-42a4e3b4a879
-- title:
--   §4, p. 39 — a T-path optimal for the scaled costs ⌊c_ij(n − 1)/εLB⌋ is longer than any T-path by at most εLB
-- statement:
--   Consider an instance of the restricted shortest path problem (vertices $1,\dots,n$, $n\ge2$, edges $(i,j)$ with $i<j$, positive integer lengths and transition times), a time budget $T$, $\varepsilon>0$ and $LB>0$. Let $p$ be a $T$-path that is optimal for the scaled lengths
--   $$\tilde c_{ij}=\Big\lfloor\frac{c_{ij}(n-1)}{\varepsilon LB}\Big\rfloor ,$$
--   i.e. $\sum_{(i,j)\in p}\tilde c_{ij}\le\sum_{(i,j)\in q}\tilde c_{ij}$ for every $T$-path $q$ (Step 2 of the Rounding Algorithm). Then every $T$-path $q$ satisfies
--   $$c(p)\le c(q)+\varepsilon\,LB .$$
--
--   This is the paper's "an $\varepsilon$-approximation can be obtained by applying Algorithm B to the scaled costs $\lfloor c_{ij}/(LB\varepsilon/(n-1))\rfloor$. The error introduced is at most $\varepsilon LB$". Combined with $LB\le$ OPT it gives the approximation ratio $1+\varepsilon$.
--
--   **Formalization Note.** The estimate holds for any $LB>0$; the hypothesis that LB is a lower bound on OPT is only needed to turn the additive error into the ratio and is not part of this statement. The upper bound $\varepsilon<1$ is omitted as unused. The paper's "$\varepsilon LB<\varepsilon OPT$" is not formalized here; with LB $=$ OPT possible it holds only as $\le$.
-- source:
--   Hassin, Approximation schemes for the restricted shortest path problem, Math. Oper. Res. 17 (1992), p. 39, §4, second paragraph and Rounding Algorithm Step 2

import Mathlib
import Definitions.Def_HassinRSP_Rounding_Setting

namespace HassinRSP.Rounding

theorem scaled_opt_error (I : Instance) (hI : I.WellFormed) (T : ℕ) (ε : ℝ) (hε0 : 0 < ε)
    (LB : ℝ) (hLB : 0 < LB) (p : List ℕ) (hp : IsRoundingOutput I T ε LB p) :
    ∀ q, IsTPath I T q → (pathLen I p : ℝ) ≤ pathLen I q + ε * LB := by sorry

end HassinRSP.Rounding
