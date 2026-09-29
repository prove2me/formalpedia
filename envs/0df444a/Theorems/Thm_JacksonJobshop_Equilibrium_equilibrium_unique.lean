-- Prove2me | Theorems.Thm_JacksonJobshop_Equilibrium_equilibrium_unique
-- name    : JacksonJobshop.Equilibrium.equilibrium_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:14:47.225492+00:00
-- url     : https://prove2.me/theorems/c2ee0aed-1456-401c-a5a6-a0e129f09eec
-- title:
--   §4, p. 135 — uniqueness of the equilibrium distribution (under bounded arrival rates)
-- statement:
--   Let $(N, L, M, R)$ be a jobshop-like queueing system satisfying Assumptions (2.1)–(2.4), and suppose its arrival rates are bounded: there is $\Lambda$ with $\lambda(K) \le \Lambda$ for all $K$. Then the system has at most one equilibrium state probability distribution: if $q$ and $q'$ are probability distributions over state vectors that are both constant solutions of the balance equations (3.1), then
--   $$q = q'.$$
--
--   Together with existence, this is what makes "the" equilibrium distribution of Theorem (4.5) well defined.
--
--   **Formalization Note** The paper asserts uniqueness without proof, citing a limit theorem for regular processes; we state uniqueness under bounded arrival rates, which holds for every example in the paper. Bounded arrival rates make the underlying Markov process non-explosive; without such a condition the model admits explosive systems with $\pi > 0$ (e.g. $N = 1$, $\lambda(K) = 4^K$, $\mu(1, k) = 2\cdot 4^{k-1}$), for which the paper's cited argument does not apply. Equations (3.1) are taken with the arrival-outflow coefficient $\lambda(S(\bar k))\sum_n r(0, n)$ (see the system definition).
-- source:
--   Jackson, Jobshop-Like Queueing Systems, Management Science 10(1) (1963), p. 135, §4, opening paragraph ('If such a distribution exists, it is unique'), with footnote 5, p. 136

import Mathlib
import Definitions.Def_JacksonJobshop_Equilibrium_System

namespace JacksonJobshop.Equilibrium

/-- Jackson (1963), p. 135, §4 opening paragraph: an equilibrium state probability distribution,
if it exists, is unique. Stated under bounded arrival rates `λ(K) ≤ Λ` (an added hypothesis:
the paper asserts uniqueness without proof, citing a limit theorem for regular processes). -/
theorem equilibrium_unique {N : ℕ} (sys : JobshopSystem N)
    (hbdd : ∃ Λ : ℝ, ∀ K, sys.lam K ≤ Λ) :
    ∀ q q' : (Fin N → ℕ) → ℝ, IsEquilibrium sys q → IsEquilibrium sys q' → q = q' := by sorry

end JacksonJobshop.Equilibrium
