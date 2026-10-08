-- Prove2me | Theorems.Thm_ObfImpossibility_RiceNoSize_exists_N
-- name    : ObfImpossibility.RiceNoSize.exists_N
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:57.143394+00:00
-- url     : https://prove2.me/theorems/db4aff50-3f4b-4623-b56d-9a0f5cbc3036
-- title:
--   Proof of Thm A.4, p. A:42 — a machine $N_{n,r}$ computing $N_{n,r}$ and running like $Z$ on $|x|\le n$
-- statement:
--   For all $n,r\in\mathbb N$ there is a machine $N$ that computes the function
--   $$N_{n,r}(x)=\begin{cases}0 & |x|\le n,\\ 1 & |x|=n+1,\\ r & |x|\ge n+2,\end{cases}$$
--   and runs in time $|x|$ with output $0$ on inputs with $|x|\le n$, exactly as $Z$ does: for all $x$ with $|x|\le n$ and all $t$,
--   $$\langle N\rangle(1^t,x)=\langle Z\rangle(1^t,x).$$
--   In particular $\langle Z\rangle(1^t,x)=\langle N\rangle(1^t,x)$ for all $t,|x|\le n$.
--
--   Together with the previous milestone this gives $S^{\langle N\rangle}()=S^{\langle Z\rangle}()=0$ once $n$ bounds the queries of $S^{\langle Z\rangle}()$.
--
--   **Formalization Note** Inputs are unary ($|x|=x$) and the output $r$ is a natural number.
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, p. A:42, proof of Theorem A.4 (the machine N_{n,r} and "For any t, |x| ≤ n, ⟨Z⟩(1^t, x) = ⟨N_{n,r}⟩(1^t, x).")

import Mathlib
import Definitions.Def_ObfImpossibility_RiceNoSize_ProofObjects

namespace ObfImpossibility.RiceNoSize

/-- p. A:42: for all `n` and `r` there is a machine `N_{n,r}` computing the function
`N_{n,r}` that runs like `Z` (in time `|x|`, output `0`) on every input `x` with `|x| ≤ n`;
in particular `⟨Z⟩(1^t, x) = ⟨N_{n,r}⟩(1^t, x)` for all `t` and all `|x| ≤ n`. -/
theorem exists_N (n r : ℕ) :
    ∃ N : Machine, fn N = Nfun n r ∧
      ∀ x : ℕ, x ≤ n → ∀ t : ℕ, bounded N t x = bounded Z t x := by sorry

end ObfImpossibility.RiceNoSize
