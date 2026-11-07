-- Prove2me | Theorems.Thm_OnlineBeckFiala_A_derivatives
-- name    : OnlineBeckFiala.A_derivatives
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:34:42.525268+00:00
-- url     : https://prove2.me/theorems/a93d0cdd-4d8c-4bed-a62a-dd6937e9dec8
-- title:
--   §3.2, display preceding (13) — $A'(y)=\frac{4y}\eta A(y)^{1+\eta/2}$ and $0\le A''(y)\le C_\eta A(y)^{1+\eta}$
-- statement:
--   Fix $\eta>0$ and let $A(y)=(1-y^2)^{-2/\eta}$ on $(-1,1)$. Then for every $y\in(-1,1)$
--   $$A'(y)=\frac{4y}\eta\,A(y)^{1+\eta/2},$$
--   and there is a constant $C_\eta>0$, depending only on $\eta$, such that for every $y\in(-1,1)$
--   $$0\le A''(y)\le C_\eta\,A(y)^{1+\eta}.$$
--
--   These derivative bounds give the curvature bound (13) for the potential $u=e^A$.
--
--   **Formalization Note** $A'$ is stated as a derivative at $y$ and $A''$ is the second iterated derivative; both are determined by $A$ near $y$.
--
--   Differences from the source:
--   - encoding: A′, A″ of A on (−1, 1) → HasDerivAt (A η) … y and iteratedDeriv 2 (A η) y for y ∈ (−1, 1); reason: A is a real function on ℝ; only its values near y ∈ (−1, 1) enter
-- source:
--   Altschuler, Tikhomirov, Online Beck–Fiala Down to Logarithmic Sparsity, arXiv:2607.14238 (held version, sha256 5a1529d2…), p.7, §3.2, display preceding (13)

import Mathlib
import Definitions.Def_OnlineBeckFiala_W

namespace OnlineBeckFiala

/-- **§3.2, display preceding (13), p.7.** Altschuler, Tikhomirov, *Online Beck–Fiala Down to
Logarithmic Sparsity*, arXiv:2607.14238 (held version, sha256 5a1529d2…): "direct differentiation
gives A′(y) = (4y/η) A(y)^{1+η/2}, 0 ≤ A″(y) ≤ C_η A(y)^{1+η}."

**Formalization Note.** For `y ∈ (−1, 1)`, where `A(y) = (1 − y²)^{−2/η}` is smooth; the constant
`C` depends only on `η`. `A″` is `iteratedDeriv 2 (A η)`, determined by `A` near `y`. -/
theorem A_derivatives (η : ℝ) (hη : 0 < η) :
    (∀ y ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt (A η) (4 * y / η * A η y ^ (1 + η / 2)) y) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
      0 ≤ iteratedDeriv 2 (A η) y ∧ iteratedDeriv 2 (A η) y ≤ C * A η y ^ (1 + η) := by sorry

end OnlineBeckFiala
