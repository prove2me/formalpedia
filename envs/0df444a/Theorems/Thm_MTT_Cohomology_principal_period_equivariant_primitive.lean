-- Prove2me | Theorems.Thm_MTT_Cohomology_principal_period_equivariant_primitive
-- name    : MTT.Cohomology.principal_period_equivariant_primitive
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-07T22:16:11.316847+00:00
-- url     : https://prove2.me/theorems/51de8e1b-f1d7-4aa0-8950-e5ab91f7d45b
-- title:
--   A principal mixed period cocycle admits an equivariant primitive
-- statement:
--   Let $N>0$, $k\ge2$, $n=k-2$, and let $g,h,v\in S_k(\Gamma_1(N))$ satisfy $\overline{v(z)}=h(-\bar z)$. Write $F_f$ for the mission's cusp primitive, normalized by $-2\pi i\int_r^{i\infty}f(z)(zX+Y)^n\,dz$, and $\rho=\operatorname{diag}(-1,1)$. Suppose $P\in\operatorname{Sym}^n\mathbb C^2$ satisfies
--   $$F_g(\gamma\infty)+\rho\cdot F_h(\rho\gamma\infty)=\gamma\cdot P-P\quad(\gamma\in\Gamma_1(N)).$$
--   Then there exists a homogeneous-polynomial-valued primitive $U$ on the upper half-plane such that
--   $$U(\gamma z)=\gamma\cdot U(z),\qquad dU=g(z)(zX+Y)^n\,dz-\overline{v(z)}(\bar zX+Y)^n\,d\bar z.$$
--   Moreover, in every cusp chart and every fixed bounded horizontal strip, each coefficient of $\delta^{-1}\cdot U(\delta z)$ has at most polynomial growth as $\operatorname{Im}z\to\infty$, for every $\delta\in\mathrm{SL}_2(\mathbb Z)$. The primitive need not tend to zero.
--
--   **Formalization Note** The derivative is expressed coefficientwise as a real Fréchet derivative on the open upper half-plane. The primitive is represented by an arbitrary extension to $\mathbb C$; no conditions are imposed outside the upper half-plane. Its derivative is unnormalized; the fixed factor $2\pi i$ in the cusp primitive is removed in passing to $U$.
-- source:
--   Columbia Spring 2021 modular-forms seminar notes, Week 4–5, §1.2, Theorem 1 and its injectivity proof, pp. 7–10, https://www.math.columbia.edu/~dmarcil/Seminars/2021_Spring/Notes/Week4-5.pdf. These four lemmas adapt the invariant-contraction/Stokes proof to the MTT mission’s binary-polynomial, reflected-summand and normalized cusp-primitive conventions; the coefficientwise derivative and finite-coset integral interfaces are explicit formalization choices.

import Definitions.Def_MTT_PeriodPairing

set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open MTT.Cohomology

theorem MTT.Cohomology.principal_period_equivariant_primitive
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (g h : CuspForm (MTT.GammaOne N) (k : ℤ)) (P : Binary ℂ)
    (hP : P ∈ Sym ℂ (k - 2))
    (hcob : ∀ γ : CongruenceSubgroup.Gamma1 N,
      cuspPrimitive g (cuspAct γ.val OnePoint.infty) +
        act !![-1, 0; 0, 1] (cuspPrimitive h
          (fractional !![-1, 0; 0, 1] (cuspAct γ.val OnePoint.infty))) =
      act γ.val.val P - P)
    (v : CuspForm (MTT.GammaOne N) (k : ℤ))
    (hv : ∀ z : UpperHalfPlane, conj (v z) = h (periodReflect z)) :
    ∃ U : ℂ → Binary ℂ, IsMixedPeriodPrimitive g v U := by sorry
