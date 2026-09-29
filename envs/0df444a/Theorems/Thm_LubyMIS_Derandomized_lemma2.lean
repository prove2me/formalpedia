-- Prove2me | Theorems.Thm_LubyMIS_Derandomized_lemma2
-- name    : LubyMIS.Derandomized.lemma2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:55:48.528984+00:00
-- url     : https://prove2.me/theorems/f99ca134-8019-4b28-92a3-dca5812aee94
-- title:
--   LEMMA 2 — Pr[X_i = R_j and X_i′ = R_j′] = n_ij·n_i′j′/q² for i ≠ i′
-- statement:
--   Let $q$ be a prime with $n \le q$ and let $A$ be an $n \times q$ matrix with entries in a set $R$. On the sample space $\{(x,y) : 0 \le x, y \le q-1\}$ with the uniform law, let $X_i(x,y) = A_{i,(x + y\cdot i) \bmod q}$. For distinct rows $i \ne i'$ and values $R_j, R_{j'}$,
--   $$\Pr[X_i = R_j \text{ and } X_{i'} = R_{j'}] = \frac{n_{ij}\, n_{i'j'}}{q^2}.$$
--
--   Together with Lemma 1 this says that $X_0, \dots, X_{n-1}$ are pairwise independent on a sample space of only $q^2$ points.
--
--   **Formalization Note** The page does not state $i \ne i'$, but the identity is false for $i = i'$ and $R_j \ne R_{j'}$ (the left side is $0$), and the page's proof uses that $i \not\equiv i' \pmod q$; the hypothesis $i \ne i'$ is added. Since $0 \le i, i' \le n - 1 < q$ when $n \le q$, distinct rows have distinct residues mod $q$.
-- source:
--   Luby, A Simple Parallel Algorithm for the Maximal Independent Set Problem, SIAM J. Comput. 15(4), 1986, p. 1045, LEMMA 2

import Mathlib
import Definitions.Def_LubyMIS_Derandomized_SampleSpace

namespace LubyMIS.Derandomized

/-- LEMMA 2 (Luby 1986, §4.2, p. 1045). On the `q²`-point sample space of §4.2, with the uniform law,
for distinct vertices `i ≠ i′`: `Pr[X_i = R_j and X_{i′} = R_{j′}] = n_{ij} n_{i′j′} / q²`. -/
theorem lemma2 (q : ℕ) [Fact q.Prime] (n : ℕ) (hnq : n ≤ q) {R : Type*} [DecidableEq R]
    (A : Fin n → ZMod q → R) (i i' : Fin n) (hii' : i ≠ i') (r r' : R) :
    ((Finset.univ.filter (fun p : ZMod q × ZMod q => Xrv A i p = r ∧ Xrv A i' p = r')).card : ℝ) /
        (q : ℝ) ^ 2 =
      ((nCount A i r : ℝ) * (nCount A i' r' : ℝ)) / (q : ℝ) ^ 2 := by sorry

end LubyMIS.Derandomized
