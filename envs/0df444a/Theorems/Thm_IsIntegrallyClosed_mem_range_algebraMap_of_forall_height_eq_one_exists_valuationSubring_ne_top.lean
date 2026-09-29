-- Prove2me | Theorems.Thm_IsIntegrallyClosed_mem_range_algebraMap_of_forall_height_eq_one_exists_valuationSubring_ne_top
-- name    : IsIntegrallyClosed.mem_range_algebraMap_of_forall_height_eq_one_exists_valuationSubring_ne_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/0e65d3a6-2540-5029-aded-8f1120ec5c5a
-- title:
--   Algebraic Hartogs lemma via valuation rings of an algebraic extension
-- statement:
--   Let $R$ be a noetherian integrally closed domain, $K$ a field equipped with an $R$-algebra structure making it a field of fractions of $R$, and $L$ a field extension of $K$ that is algebraic over $K$. Let $x \in K$ and suppose that for every prime ideal $P$ of $R$ of height $1$ there exists a valuation subring $W$ of $L$ such that: $W \neq \top$, i.e. $W$ is not all of $L$; for every $y \in K$ which can be written so that $y \cdot s = a$ in $K$ for some $a, s \in R$ with $s \notin P$ (in other words, for every element of the localisation $R_P$ viewed inside $K$), the image of $y$ under $K \to L$ lies in $W$; and the image of $x$ under $K \to L$ lies in $W$. Then $x$ lies in the range of the structure map $R \to K$, i.e. $x$ comes from an element of $R$.
--
--   This is the algebraic Hartogs lemma, $R = \bigcap_{\operatorname{ht} P = 1} R_P$ for a noetherian normal domain, in a form adapted to situations where the relevant valuation rings are given on an algebraic extension $L$ of $K$ rather than on $K$ itself. It is used in the analysis of full-level modular curves, in the criteria for the existence of a subalgebra with the prescribed localisation, formal smoothness and descent properties.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsIntegrallyClosed_mem_range_algebraMap_of_forall_height_eq_one_exists_valuationSubring_ne_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsIntegrallyClosed.mem_range_algebraMap_of_forall_height_eq_one_exists_valuationSubring_ne_top
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (x : K)
    (hx : ∀ P : Ideal R, P.IsPrime → P.height = 1 →
      ∃ W : ValuationSubring L, W ≠ ⊤ ∧
        (∀ y : K, (∃ a s : R, s ∉ P ∧ y * algebraMap R K s = algebraMap R K a) → algebraMap K L y ∈ W) ∧
        algebraMap K L x ∈ W) :
    x ∈ Set.range (algebraMap R K) := by sorry
