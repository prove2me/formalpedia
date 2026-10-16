-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_phase_sum_one_bin
-- name    : OAI.ShortEgyptian.phase_sum_one_bin
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:19:50.903808+00:00
-- url     : https://prove2.me/theorems/d391cfe6-5b57-422c-a4d1-14ba73b6abb7
-- title:
--   Exponential sum over the points where the integer part of a separated first difference is fixed
-- statement:
--   Write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}$. Let $f:\mathbb{N}\to\mathbb{R}$ and $N\in\mathbb{N}$, and write $\Delta f(n)=f(n+1)-f(n)$ for the first difference. Let $q\in\mathbb{Z}$ and let $\lambda,\beta$ be real numbers with $\lambda>0$ and $\beta>0$. Assume that the first difference increases at rate at least $\lambda$ on $\{0,\dots,N\}$:
--
--   $$
--   \lambda\,(j-i)\le\Delta f(j)-\Delta f(i)\qquad\text{for all integers }0\le i\le j\le N.
--   $$
--
--   Then the exponential sum over those $n\in\{0,\dots,N\}$ at which the integer part of $\Delta f(n)$ equals $q$ satisfies
--
--   $$
--   \Bigl|\sum_{\substack{0\le n\le N\\ \lfloor\Delta f(n)\rfloor=q}}e\bigl(f(n)\bigr)\Bigr|\le\frac{2\beta}{\lambda}+\frac1\beta+3 .
--   $$
--
--   The parameter $\beta$ is free and can be optimized afterwards; for $\beta=\sqrt\lambda$ the bound is $3/\sqrt\lambda+3$. This is the single-class step of a discrete van der Corput second-derivative estimate: splitting $\{0,\dots,N\}$ according to the value of $\lfloor\Delta f(n)\rfloor$ and adding this bound over the classes bounds the full exponential sum.
--
--   **Formalization Note** $e(x)$ is `phase x`, the complex number $\exp(2\pi i x)$. The index set is `(range (N + 1)).filter (fun n => ⌊f (n + 1) - f n⌋ = q)`; the hypothesis with $j=N$ involves the value $f(N+1)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/SecondDerivative.lean#L124-L181

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative

open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.phase_sum_one_bin (f : ℕ → ℝ) (N : ℕ) (q : ℤ) {lam β : ℝ}
    (hlam : 0 < lam) (hβ : 0 < β)
    (hsep : ∀ i j, i ≤ j → j ≤ N →
      lam * ((j : ℝ) - i) ≤ (f (j + 1) - f j) - (f (i + 1) - f i)) :
    ‖∑ n ∈ (range (N + 1)).filter (fun n => ⌊f (n + 1) - f n⌋ = q), phase (f n)‖ ≤
      2 * β / lam + 1 / β + 3 := by sorry
