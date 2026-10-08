-- Prove2me | Theorems.Thm_KedlayaUmans_Reduction_inverse_kronecker
-- name    : KedlayaUmans.Reduction.inverse_kronecker
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:01.950708+00:00
-- url     : https://prove2.me/theorems/e6cb6a0a-b1d1-44fb-9ea5-63143cbacf0a
-- title:
--   Definition 2.3 — substituting $X_i^{h^j}$ for $Y_{i,j}$ undoes $\psi_{h,\ell}$
-- statement:
--   Let $R$ be a commutative ring, $h \ge 2$, $\ell \ge 0$, and let $f \in R[X_0, \dots, X_{m-1}]$ have individual degrees at most $h^{\ell} - 1$ (every variable $X_i$ occurs with exponent at most $h^\ell - 1$). If $g = \psi_{h,\ell}(f)$, then
--   $$
--   f(X_0, \dots, X_{m-1}) = g\bigl(X_0^{h^0}, X_0^{h^1}, \dots, X_0^{h^{\ell-1}}, \dots, X_{m-1}^{h^0}, \dots, X_{m-1}^{h^{\ell-1}}\bigr),
--   $$
--   that is, substituting $X_i^{h^j}$ for $Y_{i,j}$ in $\psi_{h,\ell}(f)$ recovers $f$.
--
--   This is the sense in which $\psi_{h,\ell}$ is the inverse of the Kronecker substitution, and it is the first half of the correctness argument for the reduction of Theorem 3.1.
--
--   **Formalization Note** The substitution is `MvPolynomial.aeval` at $(i,j) \mapsto X_i^{h^j}$. The degree hypothesis is `∀ i, f.degreeOf i ≤ h ^ ℓ - 1`; since $h \ge 2$, $h^\ell \ge 1$ and the natural-number subtraction is exact.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (version of Aug. 31, 2008), p. 8, remark after Definition 2.3

import Mathlib
import Definitions.Def_KedlayaUmans_Reduction_Psi

namespace KedlayaUmans.Reduction

open MvPolynomial

theorem inverse_kronecker {R : Type*} [CommRing R] {m : ℕ} (h ℓ : ℕ) (hh : 2 ≤ h)
    (f : MvPolynomial (Fin m) R) (hf : ∀ i, f.degreeOf i ≤ h ^ ℓ - 1) :
    aeval (fun ij : Fin m × Fin ℓ => (X ij.1 : MvPolynomial (Fin m) R) ^ (h ^ (ij.2 : ℕ)))
      (psi h ℓ f) = f := by sorry

end KedlayaUmans.Reduction
