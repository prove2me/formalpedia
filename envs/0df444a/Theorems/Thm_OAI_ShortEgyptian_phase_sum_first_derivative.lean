-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_phase_sum_first_derivative
-- name    : OAI.ShortEgyptian.phase_sum_first_derivative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:19:11.558984+00:00
-- url     : https://prove2.me/theorems/5fa7d827-ebed-4941-a617-fa7a1f1a40fb
-- title:
--   Kusmin–Landau-type bound $\big|\sum_{n<N}e(f(n))\big|\le1/\beta$ for monotone increments away from the integers
-- statement:
--   Write $e(x)=\exp(2\pi i x)$ for $x\in\mathbb{R}$. Let $\beta>0$, let $f:\mathbb{N}\to\mathbb{R}$, let $q\in\mathbb{Z}$ and $N\in\mathbb{N}$, and write $\Delta(n)=f(n+1)-f(n)$ for the increments of $f$. Assume that
--
--   1. $\beta\le\Delta(n)-q\le1-\beta$ for every $n$ with $0\le n\le N$, and
--   2. $\Delta(n)\le\Delta(n+1)$ for every $n$ with $0\le n<N$, that is, $\Delta(0)\le\Delta(1)\le\dots\le\Delta(N)$.
--
--   Then
--
--   $$
--   \Big|\sum_{n=0}^{N-1}e\big(f(n)\big)\Big|\le\frac1\beta .
--   $$
--
--   This is a discrete form of the Kusmin–Landau first-derivative estimate: if the increments of the phase are nondecreasing and keep a distance at least $\beta$ from the integers $q$ and $q+1$, then the exponential sum is bounded independently of its length $N$. It is used to estimate exponential sums with smooth phases, for instance as the input to a second-derivative (van der Corput type) estimate.
--
--   **Formalization Note** The function $e$ is `phase`, and the sum runs over `Finset.range N`. Hypothesis 1 is imposed on the $N+1$ increments $\Delta(0),\dots,\Delta(N)$, which involve the values $f(0),\dots,f(N+1)$, slightly beyond the values $f(0),\dots,f(N-1)$ entering the sum; for $N=0$ the sum is empty.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/FirstDerivative.lean#L132-L198

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative

open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.phase_sum_first_derivative {β : ℝ} (hβ : 0 < β)
    (f : ℕ → ℝ) (q : ℤ) (N : ℕ)
    (hlow : ∀ n ≤ N, β ≤ f (n + 1) - f n - q)
    (hupp : ∀ n ≤ N, f (n + 1) - f n - q ≤ 1 - β)
    (hmono : ∀ n < N, f (n + 1) - f n ≤ f (n + 2) - f (n + 1)) :
    ‖∑ n ∈ range N, phase (f n)‖ ≤ 1 / β := by sorry
