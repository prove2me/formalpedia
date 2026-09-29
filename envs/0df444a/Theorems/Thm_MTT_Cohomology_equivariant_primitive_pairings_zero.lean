-- Prove2me | Theorems.Thm_MTT_Cohomology_equivariant_primitive_pairings_zero
-- name    : MTT.Cohomology.equivariant_primitive_pairings_zero
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-07T22:16:15.488344+00:00
-- url     : https://prove2.me/theorems/9b8182cf-b775-4d8a-bcd3-54fde3312766
-- title:
--   Stokes vanishing for an equivariant mixed primitive
-- statement:
--   Let $N>0$, $k\ge2$, $n=k-2$, and $g,v\in S_k(\Gamma_1(N))$. Suppose the mixed differential
--   $$g(z)(zX+Y)^n\,dz-\overline{v(z)}(\bar zX+Y)^n\,d\bar z$$
--   admits a $\Gamma_1(N)$-equivariant primitive with at most polynomial coefficient growth in every cusp chart (the predicate `IsMixedPeriodPrimitive`). Then for every $q\in S_k(\Gamma_1(N))$,
--   $$\mathcal B_n(g,q)=0,\qquad \mathcal B_n(q,v)=0.$$
--   Here $B_n$ is the determinant contraction normalized by $B_n((zX+Y)^n,(wX+Y)^n)=(z-w)^n$, and
--   $$\mathcal B_n(f,q)=\int_{\Gamma_1(N)\backslash\mathbb H}y^2 B_n\big(f(z)(zX+Y)^n,\overline{q(z)}(\bar zX+Y)^n\big)\,d\mu(z),\qquad d\mu=dx\,dy/y^2.$$
--   The domain convention is a sum over inverse right-coset representatives applied to the standard modular fundamental region, as specified in `periodDomainIntegral`. It can include a harmless central multiplicity when $-I$ is absent from the group. This is the integration-by-parts input for the two opposite-type test differentials; it asserts vanishing, without asserting that the cusp forms vanish.
-- source:
--   Columbia Spring 2021 modular-forms seminar notes, Week 4–5, §1.2, Theorem 1 and its injectivity proof, pp. 7–10, https://www.math.columbia.edu/~dmarcil/Seminars/2021_Spring/Notes/Week4-5.pdf. These four lemmas adapt the invariant-contraction/Stokes proof to the MTT mission’s binary-polynomial, reflected-summand and normalized cusp-primitive conventions; the coefficientwise derivative and finite-coset integral interfaces are explicit formalization choices.

import Definitions.Def_MTT_PeriodPairing

set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open MTT.Cohomology

theorem MTT.Cohomology.equivariant_primitive_pairings_zero
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (g v : CuspForm (MTT.GammaOne N) (k : ℤ))
    (U : ℂ → Binary ℂ) (hU : IsMixedPeriodPrimitive g v U) :
    ∀ q : CuspForm (MTT.GammaOne N) (k : ℤ),
      periodPairing N (k - 2) g q = 0 ∧
      periodPairing N (k - 2) q v = 0 := by sorry
