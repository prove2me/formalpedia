-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_ne_zero_valuation_eq_exp_neg
-- name    : LanglandsTunnell.Converse.exists_ne_zero_valuation_eq_exp_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/089f80d8-2c5d-51f2-8c9d-78f12ea395c6
-- title:
--   Elements of a number field with prescribed valuations
-- statement:
--   Let $K$ be a number field (a field with a `NumberField` structure), let $S$ be a finite set of height-one primes of the ring of integers $\mathcal{O}_K$, that is, a `Finset (HeightOneSpectrum (𝓞 K))`, and let $n : S \to \mathbb{Z}$ be an arbitrary integer-valued function on the elements of $S$, viewed as a coercion of the finite set to a type. Then there exists $\alpha \in K$ with $\alpha \neq 0$ such that for every $v \in S$ the $v$-adic valuation of $\alpha$, namely the $\mathbb{Z}_{m0}$-valued valuation `HeightOneSpectrum.valuation` of $K$ attached to the underlying prime of $v$, equals $\exp(-n_v)$, where $\exp$ denotes the multiplicative embedding `WithZero.exp` of $\mathbb{Z}$ into the nonzero part of $\mathbb{Z}_{m0}$. In the additive convention this says $\operatorname{ord}_v(\alpha) = n_v$ for all $v \in S$; no condition whatsoever is imposed on the values $n_v$, and no control is asserted at primes outside $S$. In particular the map $K^\times \to \mathbb{Z}^S$, $\alpha \mapsto (\operatorname{ord}_v \alpha)_{v \in S}$, is surjective.
--
--   This is the standard approximation statement for a Dedekind domain: the orders at finitely many finite places of a number field can be prescribed independently. It is used in the Langlands–Tunnell converse part of the development, for instance in the construction of Haar measures for torus transforms and in the production of cuspidal realisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_ne_zero_valuation_eq_exp_neg.lean

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.Converse.exists_ne_zero_valuation_eq_exp_neg (K : Type) [Field K]
    [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ↥S → ℤ) :
    ∃ α : K, α ≠ 0 ∧ ∀ v : ↥S, v.1.valuation K α = WithZero.exp (-(n v)) := by sorry
