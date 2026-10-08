-- Prove2me | Theorems.Thm_ObfImpossibility_RiceNoSize_N_mem_PiY
-- name    : ObfImpossibility.RiceNoSize.N_mem_PiY
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:55.595857+00:00
-- url     : https://prove2.me/theorems/88622a4a-36f2-4925-b58a-a8d59172b91e
-- title:
--   Proof of Thm A.4, p. A:42 — for some $r$, $\mathrm{KC}([N_{n,r}])>n+1$ and so $N_{n,r}\in\Pi_Y$
-- statement:
--   For every $n\in\mathbb N$ there is an $r\in\mathbb N$ such that
--   $$\mathrm{KC}(N_{n,r})>n+1,$$
--   and consequently every machine $N$ with $[N]=N_{n,r}$ lies in $\Pi_Y$ (it always halts, and $N_{n,r}(n+1)=1$ with $n+1<\mathrm{KC}([N])$).
--
--   In the proof of Theorem A.4 this is the machine that the simulator $S$ cannot distinguish from $Z\in\Pi_N$, although it lies in $\Pi_Y$.
--
--   **Formalization Note** The paper takes $r$ to be a string of Kolmogorov complexity $2n$ and asserts $\mathrm{KC}([N_{n,r}])>n+1$ without proof. The statement here asserts only the existence of a suitable $r$, which is all the proof uses, and does not define the Kolmogorov complexity of strings. The first conjunct rules out the degenerate value $\mathrm{KC}=0$ of a function no machine computes.
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, p. A:42, proof of Theorem A.4 ("Let r be a string of Kolmogorov complexity 2n." and "But N_{n,r} ∈ Π_Y since N_{n,r}(n+1) = 1 and KC([N_{n,r}]) > n+1.")

import Mathlib
import Definitions.Def_ObfImpossibility_RiceNoSize_ProofObjects

namespace ObfImpossibility.RiceNoSize

/-- p. A:42: for every `n` there is an `r` with `KC([N_{n,r}]) > n + 1`, and then every
machine computing `N_{n,r}` lies in `Π_Y` (since `N_{n,r}(n+1) = 1`). -/
theorem N_mem_PiY (n : ℕ) :
    ∃ r : ℕ, n + 1 < KC (Nfun n r) ∧ ∀ N : Machine, fn N = Nfun n r → N ∈ PiY := by sorry

end ObfImpossibility.RiceNoSize
