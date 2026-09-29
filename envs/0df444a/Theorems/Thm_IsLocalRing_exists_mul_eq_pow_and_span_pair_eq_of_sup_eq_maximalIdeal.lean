-- Prove2me | Theorems.Thm_IsLocalRing_exists_mul_eq_pow_and_span_pair_eq_of_sup_eq_maximalIdeal
-- name    : IsLocalRing.exists_mul_eq_pow_and_span_pair_eq_of_sup_eq_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/4ab4dc42-f1e7-5061-ad28-5414cebebff3
-- title:
--   Local equation uv=varpi^e at a transversal crossing
-- statement:
--   Let $A$ be a commutative local ring, let $\varpi \in A$ be a non-zero-divisor, and let $P, Q \subseteq A$ be prime ideals with $Q \not\subseteq P$ and $P + Q = \mathfrak m$, the maximal ideal of $A$. Suppose there are $a, b \in A$ with $P = (a, \varpi)$, $Q = (b, \varpi)$ and $ab \in \varpi A$. Suppose further that for some natural number $n$ there are $t, t' \in A$ with $t \notin Q$, $t \in \mathfrak m$ and $t t' = \varpi^{n}$. Then there exist a natural number $e$ and elements $u, v \in A$ such that $1 \le e \le n$, $uv = \varpi^{e}$, $P = (u, \varpi)$ and $Q = (v, \varpi)$. Thus the two given generating pairs for $P$ and $Q$ may be replaced by generators whose product is exactly a power of $\varpi$, with the exponent bounded by $n$; in particular $n \ge 1$ is forced by the hypotheses.
--
--   This is the commutative-algebra core of the local description of a semistable curve at an ordinary double point of the special fibre: $P$ and $Q$ cut out the two branches through the point, the hypotheses say that the fibre $A/\varpi A$ is their transversal union, and the conclusion produces the local equation $uv = \varpi^{e}$ without passing to a completion. It is used to produce oriented crossing charts for the Deligne–Rapoport models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_mul_eq_pow_and_span_pair_eq_of_sup_eq_maximalIdeal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsLocalRing.exists_mul_eq_pow_and_span_pair_eq_of_sup_eq_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A]
    {ϖ : A} (hϖ : ϖ ∈ nonZeroDivisors A)
    {P Q : Ideal A} [P.IsPrime] [Q.IsPrime] (hQP : ¬ Q ≤ P)
    (hPQ : P ⊔ Q = IsLocalRing.maximalIdeal A)
    {a b : A} (ha : Ideal.span {a, ϖ} = P) (hb : Ideal.span {b, ϖ} = Q)
    (hab : a * b ∈ Ideal.span {ϖ})
    {n : ℕ} {t t' : A} (htQ : t ∉ Q) (ht : t ∈ IsLocalRing.maximalIdeal A)
    (htt' : t * t' = ϖ ^ n) :
    ∃ (e : ℕ) (u v : A), 1 ≤ e ∧ e ≤ n ∧ u * v = ϖ ^ e ∧
      Ideal.span {u, ϖ} = P ∧ Ideal.span {v, ϖ} = Q := by sorry
