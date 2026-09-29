-- Prove2me | Theorems.Thm_HarmonicSums_even_sum_eq_half_harmonic
-- name    : HarmonicSums.even_sum_eq_half_harmonic
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:57:48.766973+00:00
-- url     : https://prove2.me/theorems/1ad34c5f-36ed-4d54-9d8f-4e6afc9233d3
-- title:
--   The sum of reciprocals of even numbers is half a harmonic number
-- statement:
--   **Reciprocals of the even numbers up to $n$ sum to half a harmonic number.**
--
--   $$\sum_{\substack{1 \le i \le n \\ i \text{ even}}} \frac{1}{i} \;=\; \frac{1}{2}\,H_{\lfloor n/2\rfloor},
--   \qquad H_m = \sum_{k=1}^{m}\frac1k .$$
--
--   Writing each even $i$ as $i = 2k$, the condition $1 \le i \le n$ becomes
--   $1 \le k \le \lfloor n/2 \rfloor$, and $\tfrac1i = \tfrac{1}{2k}$; factoring out $\tfrac12$
--   leaves exactly $H_{\lfloor n/2\rfloor}$. The floor is what makes the identity exact for both
--   parities of $n$.
--
--   The identity is the basic input for splitting a harmonic sum by parity, as in evaluating the
--   alternating harmonic sum $\sum_{i\le n}\tfrac{(-1)^{i+1}}{i} = H_n - H_{\lfloor n/2\rfloor}$,
--   and in sieve arguments where a residue class modulo $2$ is separated out before estimating the
--   remainder.
--
--   **Formalization note.** `harmonic m` is Mathlib's $H_m$ (as a rational, cast to $\mathbb{R}$),
--   and `n / 2` is natural division, i.e. $\lfloor n/2\rfloor$.
-- source:
--   Elementary. Lean proof extracted from the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace HarmonicSums

theorem even_sum_eq_half_harmonic (n : ℕ) :
    ∑ i ∈ (Finset.Icc 1 n).filter (fun i => Even i), (i : ℝ)⁻¹
      = (1 / 2 : ℝ) * harmonic (n / 2) := by sorry

end HarmonicSums
