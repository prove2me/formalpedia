-- Prove2me | Theorems.Thm_MTT_Eigenform_friedberg_hoffstein_nonzero_of_hasMinimalLevel
-- name    : MTT.Eigenform.friedberg_hoffstein_nonzero_of_hasMinimalLevel
-- status  : Open
-- author  : @riccardo.brasca
-- created : 2026-09-26T19:42:18.071987+00:00
-- url     : https://prove2.me/theorems/53ed18e0-e21d-4d48-b938-23e5d5efc96f
-- title:
--   Quadratic central nonvanishing at minimal eigenform level
-- statement:
--   Let $N>0$, let $k\ge2$ be even, and let $f$ be a normalized algebraic cuspidal Hecke eigenform of level $\Gamma_1(N)$, with arbitrary nebentype and a fixed complex embedding of its coefficients. Assume $N$ is the least positive level of an eigenform whose prime coefficients and nebentype values agree with those of $f$ outside a finite set of primes. For every integer $d>0$, there is a primitive quadratic Dirichlet character $\eta$ with
--
--   $$\operatorname{ord}(\eta)=2,\qquad (Nd,\operatorname{cond}\eta)=1,\qquad L(f,\eta,k/2)\ne0.$$
--
--   Either parity of $\eta$ is permitted. This is the primitive-level analytic input for quadratic nonvanishing; it makes no assertion about the Euler corrections of nonminimal-level eigenforms.
--
--   **Formalization Note.** The central value is the mission's Mellin integral at index $k/2-1$. The character is quadratic, so the inverse-character twist convention agrees with the usual twist. The minimal-level condition uses the current weight and does not use the legacy weight-two `IsNewEigenform` predicate. Identifying this condition with the primitive newform and specializing the automorphic nonvanishing theorem are part of this open input.
-- source:
--   Friedberg--Hoffstein, Nonvanishing theorems for automorphic L-functions on GL(2), Ann. of Math. 142 (1995), 385--423, https://doi.org/10.2307/2118638; prescribed-local-type restatement inspected in Anandavardhanan--Prasad, A local-global question in automorphic forms, Theorem 10.6, printed p.986, https://www.math.iitb.ac.in/~dprasad/comp2013.pdf. This statement is the classical minimal-level specialization with conductor avoidance; unrestricted parity permits a root-number-compatible local type. The general-nebentype twisting equation is Bettin et al., A conjectural extension of Hecke's converse theorem, equation (1.8), p.2, and Lemma 4.10, p.15, https://arxiv.org/pdf/1704.02570. Minimal level is related to primitive newforms by Atkin--Lehner--Li theory, Stein Chapter 9 Theorem 9.4, https://wstein.org/books/modform/modform/newforms.html.

import Definitions.Def_MTT_HeckeEquivalence
import Definitions.Def_KN_HorizontalPadicL

set_option autoImplicit false

open HorizontalPadicL

/-- Quadratic central nonvanishing with finite conductor avoidance for an eigenform
at the least positive level of its Hecke system. No parity is imposed on the twist. -/
theorem MTT.Eigenform.friedberg_hoffstein_nonzero_of_hasMinimalLevel
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (heven : Even k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (hmin : f.HasMinimalLevel) (d : ℕ) (hd : 0 < d) :
    ∃ η : DirichletCharacterWithLevel,
      η.2.IsPrimitive ∧
      orderOf η.2 = 2 ∧
      Nat.Coprime (N * d) η.2.conductor ∧
      @MTT.criticalLValue ι f.form
        η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2 (k / 2 - 1) ≠ 0 := by sorry
