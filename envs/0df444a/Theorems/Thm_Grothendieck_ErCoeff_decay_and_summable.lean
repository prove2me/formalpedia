-- Prove2me | Theorems.Thm_Grothendieck_ErCoeff_decay_and_summable
-- name    : Grothendieck.ErCoeff_decay_and_summable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T16:01:24.268208+00:00
-- url     : https://prove2.me/theorems/c3e9894a-0770-48a6-bd31-de8a04f64f95
-- title:
--   Coefficient decay of $E_r$ and summability on the closed disc
-- statement:
--   For every integer $r\ge2$ the coefficients of the paper's series satisfy
--
--   $$\mathrm{ErCoeff}_r(k)\ \le\ \frac{C_r}{(k+1)^2},\qquad C_r=\frac2r\Big(\frac{\Gamma((r+1)/2)}{\Gamma(r/2)}\Big)^2,$$
--
--   and consequently, for every complex $w$ with $\lVert w\rVert\le1$, the series
--   $\sum_k \mathrm{ErCoeff}_r(k)w^k$ converges.
--
--   The bound is a Wallis-type estimate on the ratio
--   $\mathrm{ErCoeff}_r(k)/C_r=\frac{(1/2)_k^2}{(r/2+1)_k\,k!}$, which behaves like $k^{-2}$: the sequence
--   $k\mapsto \mathrm{ErCoeff}_r(k)(k+1)^2$ is decreasing for $r\ge2$, so its value at $k=0$ bounds it.
--
--   Why it matters is a Lean-specific point that is easy to miss. `tsum` of a non-summable family is $0$
--   by convention, so a statement about $\sum_k a_kw^k$ at $\lVert w\rVert=1$ — in particular at
--   $w=\pm1$, i.e. at $t=\pm1$ — is *false as written* unless summability on the closed disc is
--   available. Every evaluation of $E_r$ at $t=\pm1$, and the endpoint case of Proposition 4.2, needs
--   this. The decay also gives absolute convergence of the complex series on the closed disc, which is
--   what the contour arguments of §3 use.
--
--   **Formalization Note** `ErCoeff`, `Cr` are the mission's definitions. This is a supporting lemma, not
--   a verbatim statement of the paper.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — the coefficients (2.1), p. 84, and the convergence statements of Section 3, p. 88.

import Mathlib
import Definitions.Def_Grothendieck_Series

open scoped BigOperators Real

namespace Grothendieck

/-- **Decay of the rank-`r` coefficients and summability on the closed disc.** For `r ≥ 2` the
coefficients of `E_r` satisfy `ErCoeff r k ≤ Cr r / (k+1)²`, and consequently the series
`Σ_k ErCoeff r k · w^k` converges for every complex `w` with `‖w‖ ≤ 1` — in particular at
`w = ±1`, where a bare `tsum` would otherwise be `0` by convention. -/
theorem ErCoeff_decay_and_summable (r : ℕ) (hr : 2 ≤ r) :
    (∀ k : ℕ, ErCoeff r k ≤ Cr r / ((k : ℝ) + 1) ^ 2) ∧
      (∀ w : ℂ, ‖w‖ ≤ 1 → Summable (fun k : ℕ => (ErCoeff r k : ℂ) * w ^ k)) := by sorry

end Grothendieck
