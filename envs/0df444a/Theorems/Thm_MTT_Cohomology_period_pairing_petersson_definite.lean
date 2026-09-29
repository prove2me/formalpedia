-- Prove2me | Theorems.Thm_MTT_Cohomology_period_pairing_petersson_definite
-- name    : MTT.Cohomology.period_pairing_petersson_definite
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-07T22:16:20.750418+00:00
-- url     : https://prove2.me/theorems/d69c5708-3b32-4ff4-ad79-680dfffad1a3
-- title:
--   The period contraction is a nonzero multiple of the Petersson norm
-- statement:
--   Let $N>0$, $k\ge2$, $n=k-2$, and $f\in S_k(\Gamma_1(N))$. The determinant contraction and Petersson product, with the same domain convention, satisfy
--   $$\mathcal B_n(f,f)=(2i)^n\langle f,f\rangle_{\mathrm{Pet}},\qquad \mathcal B_n(f,f)=0\Longleftrightarrow f=0.$$
--   Here $\mathcal B_n$ contracts $f(z)(zX+Y)^n$ with its conjugate and multiplies by $y^2$ before integrating against hyperbolic measure. The Petersson product is the integral of $|f(z)|^2 y^k$ against that measure. Both use the sum of integrals on the standard modular fundamental region over inverse right-coset representatives for $\Gamma_1(N)$ in $\mathrm{SL}_2(\mathbb Z)$.
--
--   The statement includes weight two. It records both the exact nonzero normalization and definiteness. Establishing convergence of these explicitly defined integrals is part of this analytic obligation; no integrability or finite-dimensionality assumption is imposed on the cusp form.
-- source:
--   Columbia Spring 2021 modular-forms seminar notes, Week 4–5, §1.2, Theorem 1 and its injectivity proof, pp. 7–10, https://www.math.columbia.edu/~dmarcil/Seminars/2021_Spring/Notes/Week4-5.pdf. These four lemmas adapt the invariant-contraction/Stokes proof to the MTT mission’s binary-polynomial, reflected-summand and normalized cusp-primitive conventions; the coefficientwise derivative and finite-coset integral interfaces are explicit formalization choices.

import Definitions.Def_MTT_PeriodPairing

set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open MTT.Cohomology

theorem MTT.Cohomology.period_pairing_petersson_definite
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (f : CuspForm (MTT.GammaOne N) (k : ℤ)) :
    periodPairing N (k - 2) f f =
      (2 * Complex.I) ^ (k - 2) * periodPetersson N k f f ∧
    (periodPairing N (k - 2) f f = 0 ↔ f = 0) := by sorry
