-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_isAdicComplete_adicCompletionIntegers
-- name    : IsDedekindDomain.HeightOneSpectrum.isAdicComplete_adicCompletionIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/87ade033-4b2a-5b9c-b076-dff2eb6405d3
-- title:
--   Completion at a finite place is adically complete
-- statement:
--   Let $R$ be a commutative ring which is a Dedekind domain, let $K$ be a field equipped with an $R$-algebra structure making it a fraction field of $R$, and let $v$ be a point of the height-one spectrum of $R$, i.e. a nonzero prime ideal of $R$. Write $K_v =$ `v.adicCompletion K` for the completion of $K$ at $v$, a valued field with valuation taking values in $\mathbb{Z}_{m0} =$ `WithZero (Multiplicative ℤ)`, and $\mathcal{O}_v =$ `v.adicCompletionIntegers K` for the valuation subring of $K_v$. The theorem asserts that $\mathcal{O}_v$, viewed as a module over itself, is adically complete for the maximal ideal $\mathfrak{m}_v$ of the local ring $\mathcal{O}_v$: the $\mathfrak{m}_v$-adic filtration is Hausdorff, that is, an element lying in $\mathfrak{m}_v^n$ for every $n$ is zero, and every sequence $(f_n)$ in $\mathcal{O}_v$ with $f_m \equiv f_n \bmod \mathfrak{m}_v^m$ for all $m \le n$ has a limit $L \in \mathcal{O}_v$ with $f_n \equiv L \bmod \mathfrak{m}_v^n$ for all $n$. Equivalently, $\mathcal{O}_v \to \varprojlim_n \mathcal{O}_v/\mathfrak{m}_v^n$ is an isomorphism.
--
--   This is the standard fact that the valuation ring of a completed local field is complete for its maximal-ideal-adic topology, in the form of the `IsAdicComplete` hypothesis required by results on local fields and on Galois representations attached to automorphic and modular forms, where $\mathcal{O}_v$ is used as a complete discrete valuation ring of coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_isAdicComplete_adicCompletionIntegers.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u v
open IsDedekindDomain

theorem IsDedekindDomain.HeightOneSpectrum.isAdicComplete_adicCompletionIntegers
    {R : Type u} [CommRing R] [IsDedekindDomain R] (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) :
    IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K) := by sorry
