-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_isRoot_and_valued_sub_mul_le_of_valued_eval_lt
-- name    : IsDedekindDomain.HeightOneSpectrum.exists_isRoot_and_valued_sub_mul_le_of_valued_eval_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/ee538f44-3ae8-5d8c-8928-bdaaef3577c8
-- title:
--   Hensel's lemma with |f(a₀)| < |f'(a₀)|² over Kᵥ
-- statement:
--   Let $K$ be a number field, let $v$ be a height-one prime of its ring of integers $\mathcal{O}_K$, let $K_v$ denote the completion of $K$ at $v$ with its canonical valuation $\mathrm{v}$ (normalised so that elements of the valuation ring have value at most $1$), and let $\mathcal{O}_v \subseteq K_v$ be the ring of integers of that completion. Let $f$ be a polynomial with coefficients in $\mathcal{O}_v$ and let $a_0 \in \mathcal{O}_v$ satisfy the strict inequality $\mathrm{v}(f(a_0)) < \mathrm{v}(f'(a_0))^2$ between values in the value group (with zero) of $K_v$, where $f'$ is the formal derivative of $f$ and both values are computed on the images of $f(a_0)$ and $f'(a_0)$ in $K_v$. The conclusion is that there exists $a \in \mathcal{O}_v$ which is a root of $f$, that is $f(a) = 0$, and which satisfies $\mathrm{v}(a - a_0)\,\mathrm{v}(f'(a_0)) \le \mathrm{v}(f(a_0))$, the difference and the values again being taken in $K_v$. No monicity or degree hypothesis is imposed on $f$, and $f'(a_0)$ is allowed to lie in the maximal ideal of $\mathcal{O}_v$.
--
--   This is Hensel's lemma in its strong (Newton-approximation) form for the completion of a number field at a finite place, giving both the existence of a root and the quantitative estimate on its distance from the approximate root. It is used to produce $n$-th roots of principal units in $\mathcal{O}_v$, via $f = X^n - a$ and $a_0 = 1$, including the case where the residue characteristic divides $n$; in the formalisation it is cited by [`IsDedekindDomain.HeightOneSpectrum.exists_forall_exists_pow_eq_of_valued_sub_one_le`](thm.html#IsDedekindDomain.HeightOneSpectrum.exists_forall_exists_pow_eq_of_valued_sub_one_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_exists_isRoot_and_valued_sub_mul_le_of_valued_eval_lt.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain

theorem IsDedekindDomain.HeightOneSpectrum.exists_isRoot_and_valued_sub_mul_le_of_valued_eval_lt
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (f : Polynomial ↥(v.adicCompletionIntegers K)) (a₀ : ↥(v.adicCompletionIntegers K))
    (h : Valued.v ((f.eval a₀ : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K) <
      Valued.v ((f.derivative.eval a₀ : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K) ^ 2) :
    ∃ a : ↥(v.adicCompletionIntegers K), f.IsRoot a ∧
      Valued.v ((a : v.adicCompletion K) - (a₀ : v.adicCompletion K)) *
          Valued.v ((f.derivative.eval a₀ : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K) ≤
        Valued.v ((f.eval a₀ : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K) := by sorry
