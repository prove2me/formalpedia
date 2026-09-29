-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_finset_card_eq_absNorm_indicator_ball_eq_sum_rat
-- name    : IsDedekindDomain.HeightOneSpectrum.exists_finset_card_eq_absNorm_indicator_ball_eq_sum_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/a36a7b81-d393-56b7-8be1-9f90f223ecc8
-- title:
--   Refining a ball of ℚₚ into q balls: indicator identity
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$, let $n$ be an integer, and let $t$ be an element of the completion $\mathbb{Q}_p$ of $\mathbb{Q}$ at $p$, equipped with its canonical valuation $v$ taking values in $\mathbb{Z}^{\mathrm{mult}}$ adjoined with $0$. The assertion is that there exists a finite subset $S$ of $\mathbb{Q}_p$ whose cardinality equals $\mathrm{absNorm}$ of the ideal $p$ (the index of $p$ in the ring of integers, i.e. the residue cardinality $q$), such that for every $x \in \mathbb{Q}_p$ the complex number which is $1$ if $v(x-t) \le \exp(-n)$ and $0$ otherwise equals the sum over $s \in S$ of the complex numbers which are $1$ if $v(x-s) \le \exp(-(n+1))$ and $0$ otherwise. Thus the closed ball of radius $\exp(-n)$ about $t$ is covered by the $q$ closed balls of radius $\exp(-(n+1))$ about the points of $S$, and the identity of indicator functions encodes both that the covering is exact and that the smaller balls are pairwise disjoint and contained in the larger one; disjointness is not stated separately.
--
--   This is the elementary ultrametric fact that a ball in a discretely valued field with finite residue field of cardinality $q$ splits into $q$ balls of the next smaller radius, recorded in the form of an identity between indicator functions of complex value. It is used in the analysis of step functions on $\mathbb{Q}_p$ that enters the proof that a unitary principal series representation of $\mathrm{GL}_2(\mathbb{Q}_p)$ admits no determinant-equivariant functional.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_exists_finset_card_eq_absNorm_indicator_ball_eq_sum_rat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem IsDedekindDomain.HeightOneSpectrum.exists_finset_card_eq_absNorm_indicator_ball_eq_sum_rat
    (p : HeightOneSpectrum (𝓞 ℚ)) (n : ℤ) (t : p.adicCompletion ℚ) :
    ∃ S : Finset (p.adicCompletion ℚ), S.card = Ideal.absNorm p.asIdeal ∧
      ∀ x : p.adicCompletion ℚ,
        (if Valued.v (x - t) ≤ WithZero.exp (-n) then (1 : ℂ) else 0) =
          ∑ s ∈ S, (if Valued.v (x - s) ≤ WithZero.exp (-(n + 1)) then (1 : ℂ) else 0) := by sorry
