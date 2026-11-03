-- Prove2me | Theorems.Thm_Grothendieck_Er_strictMono_Icc
-- name    : Grothendieck.Er_strictMono_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T14:41:32.775224+00:00
-- url     : https://prove2.me/theorems/986fefe5-f575-49f7-97db-46922abb7e9d
-- title:
--   $E_r$ is strictly increasing on the whole interval $[-1,1]$
-- statement:
--   For every integer $r\ge1$ and all $-1\le s<t\le1$,
--
--   $$
--   E_r(s)<E_r(t),
--   $$
--
--   so $E_r$ is strictly increasing, hence injective, on its whole interval $[-1,1]$.
--
--   The series $E_r(t)=\sum_k a_k t^{2k+1}$ has nonnegative coefficients $a_k=C_r(1/2)_k^2/((r/2+1)_k k!)$ and $E_r(0)=0$, and $E_r$ is odd. Three facts combine: on $[0,1]$ the difference of the two series is a series of positive terms (each $a_k(t^{2k+1}-s^{2k+1})>0$ for $t>s\ge0$), summable because $\sum_k a_k$ converges; on the negative half oddness reduces to the positive one; and across the origin $E_r(s)<0<E_r(t)$ because every term of the series is nonnegative at $t>0$ while the first term is $C_r\,t>0$.
--
--   This is what makes the paper's §3 well posed. The paper Taylor-expands the inverse function $E_r^{-1}$ and evaluates it at $t\,\beta(r,G)$; injectivity on $[-1,1]$ is exactly the property that the inverse inherited from the definition is the genuine inverse, and the survey of §4 uses $E_r^{-1}(\beta f(u)\cdot f(v))$ for arbitrary $f$.
--
--   **Formalization Note** A supporting lemma rather than a verbatim statement of the paper: it extends the strict monotonicity of $E_r$ from $[0,1]$ (node `Grothendieck.Er_strictMono`) to the full interval, using oddness (`Grothendieck.Er_one`, `Er_neg`) and the positivity of the coefficients.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — Section 3, p. 88 (positivity of the coefficients, invertibility of $E_r$) and Section 4, p. 92 (use of $E_r^{-1}$).

import Mathlib
import Definitions.Def_Grothendieck_Series

open scoped BigOperators Real

namespace Grothendieck

/-- **Strict monotonicity of `E_r` on its whole interval.** For `r ≥ 1` and `-1 ≤ s < t ≤ 1`,
`E_r(s) < E_r(t)`; in particular `E_r` is injective on `[-1,1]`, which is what makes the paper's
inverse function `E_r⁻¹` well defined. -/
theorem Er_strictMono_Icc {r : ℕ} (hr : 1 ≤ r) {s t : ℝ}
    (hs : s ∈ Set.Icc (-1 : ℝ) 1) (hst : s < t) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    Er r s < Er r t := by sorry

end Grothendieck
