-- Prove2me | Theorems.Thm_MTT_Cohomology_period_reflected_cusp_form
-- name    : MTT.Cohomology.period_reflected_cusp_form
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-07T22:16:07.065178+00:00
-- url     : https://prove2.me/theorems/a8792033-47ea-4c08-bbef-59a4cbb2477a
-- title:
--   Reflection identifies the antiholomorphic cusp-form summand
-- statement:
--   Let $N>0$, $k\ge2$, and $h\in S_k(\Gamma_1(N))$. Reflection defines a cusp form $v$ of the same level and weight, with
--   $$v(z)=\overline{h(-\bar z)},\qquad v=0\Longleftrightarrow h=0.$$
--   This identifies the reflected period summand with an antiholomorphic differential. Specifically, if $\rho=\operatorname{diag}(-1,1)$, $\jmath(z)=-\bar z$ and $n=k-2$, then pulling back $h(z)(zX+Y)^n\,dz$ by $\jmath$ and applying $\rho$ to coefficients gives $-\overline{v(z)}(\bar zX+Y)^n\,d\bar z$. The displayed cusp-form existence and zero equivalence are the formal assertion; the differential identity explains its convention.
-- source:
--   Columbia Spring 2021 modular-forms seminar notes, Week 4–5, §1.2, Theorem 1 and its injectivity proof, pp. 7–10, https://www.math.columbia.edu/~dmarcil/Seminars/2021_Spring/Notes/Week4-5.pdf. These four lemmas adapt the invariant-contraction/Stokes proof to the MTT mission’s binary-polynomial, reflected-summand and normalized cusp-primitive conventions; the coefficientwise derivative and finite-coset integral interfaces are explicit formalization choices.

import Definitions.Def_MTT_PeriodPairing

set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open MTT.Cohomology

theorem MTT.Cohomology.period_reflected_cusp_form
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (h : CuspForm (MTT.GammaOne N) (k : ℤ)) :
    ∃ v : CuspForm (MTT.GammaOne N) (k : ℤ),
      (∀ z : UpperHalfPlane, conj (v z) = h (periodReflect z)) ∧
      (v = 0 ↔ h = 0) := by sorry
