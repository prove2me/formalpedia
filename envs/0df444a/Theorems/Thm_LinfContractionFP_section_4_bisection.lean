-- Prove2me | Theorems.Thm_LinfContractionFP_section_4_bisection
-- name    : LinfContractionFP.section_4_bisection
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:14:31.841801+00:00
-- url     : https://prove2.me/theorems/9c8713c5-1fe4-4821-b174-8149c31aa79d
-- title:
--   Section 4 — bisection in dimension one
-- statement:
--   There is a universal constant $C$ such that for every $0<\gamma\le1$, every $(1-\gamma)$-contraction $f$ of $[0,1]$ and every $\varepsilon>0$, bisection on $f(x)-x$ returns an $\varepsilon$-near fixed point of $f$ after at most
--   $$C\,\big(1+\max\{0,\log(1/\varepsilon)\}\big)$$
--   evaluations of $f$.
--
--   This is the base case $d=1$ of Solve.
--
--   Differences from the source:
--   - reading: O(1 + log(1/ε)) evaluations → at most C(1 + max 0 (log(1/ε))) evaluations for one universal C; reason: the O-bound with its constant made explicit; for ε ≤ 1 the max is log(1/ε), and for ε > 1, where 1 + log(1/ε) can be negative, bisection makes no evaluation
--   - reading: bisection on f(x) − x → a ← m if f(m) − m ≥ 0, else b ← m; reason: the page does not fix the tie f(m) = m; either side keeps x* in the interval
--   - encoding: f : [0,1] → [0,1] → f : (Fin 1 → ℝ) → (Fin 1 → ℝ); reason: dimension one as a one-coordinate vector
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Section 4, p.6

import Mathlib
import Definitions.Def_LinfContractionFP_IsContraction
import Definitions.Def_LinfContractionFP_IsNearFixed
import Definitions.Def_LinfContractionFP_bisect

namespace LinfContractionFP

/-- Section 4, the base case `d = 1`: bisection on `f(x) − x` returns an `ε`-near fixed point of a
`(1 − γ)`-contraction of `[0, 1]` using `O(1 + log(1/ε))` evaluations of `f`.

Soleymani–Farina, *A Quasipolynomial Algorithm for ℓ∞ Contractions*, arXiv:2610.30122 (held
version, sha256 595b4493…), Section 4, p.6: "In dimension one, Solve(f, ε) uses bisection on f(x) − x. Indeed,
f(0) ≥ 0, f(1) ≤ 1, and f(x) − x is strictly decreasing by contractivity. Thus, bisection
maintains an interval containing x*, and returning its midpoint once the interval has length at
most 2ε yields an ε-near fixed point using O(1 + log(1/ε)) evaluations of f."

**Formalization Note.** One universal constant `C` serves every `γ`, `f` and `ε`. The bound is
written `C (1 + max 0 (log(1/ε)))`: for `ε ≤ 1` this is the printed `C (1 + log(1/ε))`; for
`ε > 1`, where the printed expression can be negative, bisection makes no evaluation. -/
theorem section_4_bisection : ∃ C : ℝ, ∀ γ : ℝ, 0 < γ → γ ≤ 1 →
    ∀ f : (Fin 1 → ℝ) → (Fin 1 → ℝ), IsContraction γ f → ∀ ε : ℝ, 0 < ε →
      IsNearFixed f ε (bisect f ε).1 ∧
        ((bisect f ε).2 : ℝ) ≤ C * (1 + max 0 (Real.log (1 / ε))) := by sorry

end LinfContractionFP
