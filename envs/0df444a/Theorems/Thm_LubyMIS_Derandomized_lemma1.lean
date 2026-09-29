-- Prove2me | Theorems.Thm_LubyMIS_Derandomized_lemma1
-- name    : LubyMIS.Derandomized.lemma1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:55:17.884605+00:00
-- url     : https://prove2.me/theorems/c2c9a9c3-8081-4ecf-8ac5-026d2964c8cd
-- title:
--   LEMMA 1 — Pr[X_i = R_j] = n_ij/q on the q²-point sample space
-- statement:
--   Let $q$ be a prime with $n \le q$ and let $A$ be an $n \times q$ matrix with entries in a set $R$. On the sample space $\{(x,y) : 0 \le x, y \le q-1\}$ with the uniform law, let $X_i(x,y) = A_{i,(x + y\cdot i) \bmod q}$. For every row $i$ and every value $R_j$, if $n_{ij}$ is the number of entries of row $i$ equal to $R_j$, then
--   $$\Pr[X_i = R_j] = \frac{n_{ij}}{q}.$$
--
--   Thus each $X_i$ has exactly the marginal law prescribed by row $i$ of $A$.
--
--   **Formalization Note** The probability is the number of sample points $(x,y) \in (\mathbb{Z}/q\mathbb{Z})^2$ with $X_i(x,y) = R_j$, divided by $q^2$. The hypothesis $n \le q$ is §4.1's criterion 1.
-- source:
--   Luby, A Simple Parallel Algorithm for the Maximal Independent Set Problem, SIAM J. Comput. 15(4), 1986, p. 1045, LEMMA 1

import Mathlib
import Definitions.Def_LubyMIS_Derandomized_SampleSpace

namespace LubyMIS.Derandomized

/-- LEMMA 1 (Luby 1986, §4.2, p. 1045). On the `q²`-point sample space of §4.2, with the uniform law,
`Pr[X_i = R_j] = n_{ij}/q`. -/
theorem lemma1 (q : ℕ) [Fact q.Prime] (n : ℕ) (hnq : n ≤ q) {R : Type*} [DecidableEq R]
    (A : Fin n → ZMod q → R) (i : Fin n) (r : R) :
    ((Finset.univ.filter (fun p : ZMod q × ZMod q => Xrv A i p = r)).card : ℝ) / (q : ℝ) ^ 2 =
      (nCount A i r : ℝ) / q := by sorry

end LubyMIS.Derandomized
