-- Prove2me | Theorems.Thm_Leopoldt_nonempty_primesOver
-- name    : Leopoldt.nonempty_primesOver
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-03T08:59:27.482833+00:00
-- url     : https://prove2.me/theorems/fb5d462c-e9e5-474b-971c-de6bbe99c561
-- title:
--   A number field has a prime above every rational prime $p$
-- statement:
--   Let $p$ be a prime number and $K$ a number field with ring of integers $\mathcal{O}_K$. The set of primes of $K$ above $p$ is
--   $$P_p(K) = \{\mathfrak{p} \subset \mathcal{O}_K \text{ a nonzero prime ideal} : p \in \mathfrak{p}\}.$$
--   The statement asserts that this set is nonempty: there is at least one nonzero prime ideal of $\mathcal{O}_K$ that contains $p$.
--
--   This is the lying-over property of the integral extension $\mathbb{Z} \subset \mathcal{O}_K$ applied to the maximal ideal $p\mathbb{Z}$, or equivalently the fact that $p$ is not a unit of $\mathcal{O}_K$ and therefore lies in some maximal ideal, which is a nonzero prime of the Dedekind domain $\mathcal{O}_K$.
--
--   **Use.** Several statements about the semilocal units $\prod_{\mathfrak{p} \mid p} \mathcal{O}_{K_\mathfrak{p}}^\times$ and the semilocal $p$-adic logarithm need to fix one prime $v_0 \mid p$ of $K$ to work at; this lemma supplies it. It is the first step of the reduction of `Leopoldt.exists_linearIndependent_log_conj_of_brumer` (Ax's deduction of Leopoldt's conjecture from Brumer's theorem).
--
--   **Formalization Note.** `Leopoldt.PrimesOver p K` is the subtype of the height-one spectrum of $\mathcal{O}_K$ (nonzero prime ideals) consisting of the primes containing the image of $p$; the statement is `Nonempty` of that subtype. The hypothesis that $p$ is prime is carried as a `Fact` instance.
-- source:
--   Lying-over for the integral extension $\mathbb{Z} \subset \mathcal{O}_K$: J. Neukirch, Algebraic Number Theory, Springer 1999, Chapter I, Section 8 (Extensions of Dedekind domains), cited by section; equivalently, $p$ is not a unit of $\mathcal{O}_K$ and lies in a maximal ideal. Stated for the platform type `Leopoldt.PrimesOver p K` of `Definitions.Def_LeopoldtDefect`.

import Definitions.Def_LeopoldtDefect

open NumberField

theorem Leopoldt.nonempty_primesOver (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K] :
    Nonempty (Leopoldt.PrimesOver p K) := by sorry
