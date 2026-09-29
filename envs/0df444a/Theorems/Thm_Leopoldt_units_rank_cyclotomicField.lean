-- Prove2me | Theorems.Thm_Leopoldt_units_rank_cyclotomicField
-- name    : Leopoldt.units_rank_cyclotomicField
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:17:05.426395+00:00
-- url     : https://prove2.me/theorems/ba6a8a24-2237-4502-9318-8fd0a884ebc5
-- title:
--   Unit rank of $\mathbb{Q}(\zeta_n)$ is $\varphi(n)/2 - 1$
-- statement:
--   Let $n \ge 0$ be a natural number and let $\mathbb{Q}(\zeta_n)$ be the $n$-th cyclotomic field. Its unit rank, i.e. the $\mathbb{Z}$-rank $r_1 + r_2 - 1$ of the unit group of its ring of integers given by Dirichlet's unit theorem, is
--
--   $$
--   \operatorname{rank} \mathcal{O}_{\mathbb{Q}(\zeta_n)}^{\times} \;=\; \Big\lfloor \frac{\varphi(n)}{2} \Big\rfloor - 1 ,
--   $$
--
--   where $\varphi$ is Euler's totient function and the subtraction is truncated at $0$.
--
--   For $n > 2$ the field $\mathbb{Q}(\zeta_n)$ has degree $\varphi(n)$ and is totally complex, so $r_1 = 0$, $r_2 = \varphi(n)/2$ and the rank is $\varphi(n)/2 - 1$. For $n \in \{0, 1, 2\}$ the field is $\mathbb{Q}$ and the rank is $0$, which the formula also gives since $\lfloor \varphi(n)/2 \rfloor = 0$. In particular the unit rank is at most $1$ exactly when $\varphi(n) \le 4$, i.e. for the fields $\mathbb{Q}$, $\mathbb{Q}(\zeta_3)$, $\mathbb{Q}(i)$, $\mathbb{Q}(\zeta_5)$, $\mathbb{Q}(\zeta_8)$, $\mathbb{Q}(\zeta_{12})$; this is the range in which statements about the unit group of cyclotomic fields (such as Leopoldt's conjecture) are elementary.
--
--   **Formalization Note.** `CyclotomicField n ℚ` is Mathlib's splitting field of the $n$-th cyclotomic polynomial over $\mathbb{Q}$; for $n = 0$ that polynomial is the constant $1$ and the field is $\mathbb{Q}$. Natural-number division and subtraction are truncating, matching $\lfloor \varphi(n)/2 \rfloor - 1$ with $0 - 1 = 0$.
-- source:
--   L. C. Washington, Introduction to Cyclotomic Fields (2nd ed., GTM 83, Springer 1997), Theorem 2.5 ([Q(zeta_n):Q] = phi(n)) and Chapter 5 (Q(zeta_n) for n>2 is totally complex, hence by Dirichlet's unit theorem its unit rank is phi(n)/2 - 1). Formal ingredients: Mathlib IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two and NumberField.InfinitePlace.card_add_two_mul_card_eq_rank.

import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

open NumberField

namespace Leopoldt
theorem units_rank_cyclotomicField (n : ℕ) :
    Units.rank (CyclotomicField n ℚ) = n.totient / 2 - 1 := by sorry
end Leopoldt
