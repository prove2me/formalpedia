-- Prove2me | Theorems.Thm_OnlineBeckFiala_eq_13
-- name    : OnlineBeckFiala.eq_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:34:46.574242+00:00
-- url     : https://prove2.me/theorems/6211fba0-136a-4f82-8f08-f38a54d3aa66
-- title:
--   Eq. (13) — $0\le u''=u(A'^2+A'')\le C_\eta u(\log u)^{2+\eta}$
-- statement:
--   Fix $\eta>0$ and let $u=e^A$ with $A(y)=(1-y^2)^{-2/\eta}$ on $(-1,1)$. There is a constant $C_\eta>0$, depending only on $\eta$, such that for every $y\in(-1,1)$
--   $$0\le u''(y)=u(y)\bigl((A'(y))^2+A''(y)\bigr)\le C_\eta\,u(y)\bigl(\log u(y)\bigr)^{2+\eta}.$$
--
--   This is the curvature bound (11) with $p=2+\eta$ for the chosen potential; it is the input to Lemma 3.1.
--
--   **Formalization Note** All three parts are stated: nonnegativity, the identity, and the bound. $u''$ and $A''$ are second iterated derivatives.
--
--   Differences from the source:
--   - encoding: u″, A′, A″ on (−1, 1) → iteratedDeriv 2 (u η) y, deriv (A η) y, iteratedDeriv 2 (A η) y for y ∈ (−1, 1); reason: u and A are real functions on ℝ; only their values near y enter
-- source:
--   Altschuler, Tikhomirov, Online Beck–Fiala Down to Logarithmic Sparsity, arXiv:2607.14238 (held version, sha256 5a1529d2…), p.7, §3.2, eq. (13)

import Mathlib
import Definitions.Def_OnlineBeckFiala_W

namespace OnlineBeckFiala

/-- **Eq. (13), §3.2, p.7.** Altschuler, Tikhomirov, *Online Beck–Fiala Down to Logarithmic
Sparsity*, arXiv:2607.14238 (held version, sha256 5a1529d2…): "Since A ≥ 1, we obtain
0 ≤ u″(y) = u(y)((A′(y))² + A″(y)) ≤ C_η u(y)(log u(y))^{2+η}. (13)"

**Formalization Note.** For `y ∈ (−1, 1)`; `u″`, `A′`, `A″` are `iteratedDeriv 2 (u η)`,
`deriv (A η)`, `iteratedDeriv 2 (A η)`; the constant `C` depends only on `η`. -/
theorem eq_13 (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
      0 ≤ iteratedDeriv 2 (u η) y ∧
      iteratedDeriv 2 (u η) y = u η y * ((deriv (A η) y) ^ 2 + iteratedDeriv 2 (A η) y) ∧
      iteratedDeriv 2 (u η) y ≤ C * u η y * (Real.log (u η y)) ^ (2 + η) := by sorry

end OnlineBeckFiala
