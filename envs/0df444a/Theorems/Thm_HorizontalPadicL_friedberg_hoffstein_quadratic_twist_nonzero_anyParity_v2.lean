-- Prove2me | Theorems.Thm_HorizontalPadicL_friedberg_hoffstein_quadratic_twist_nonzero_anyParity_v2
-- name    : HorizontalPadicL.friedberg_hoffstein_quadratic_twist_nonzero_anyParity_v2
-- status  : Open
-- author  : @davidloeffler
-- created : 2026-09-25T11:30:33.101433+00:00
-- url     : https://prove2.me/theorems/845f44da-c403-401d-a0e3-995ef0b3fc31
-- title:
--   A nonvanishing quadratic seed with finite conductor avoidance and unrestricted parity
-- statement:
--   Let $N>0$ and let $k\ge2$ be even. Let $f$ be a normalized algebraic cuspidal Hecke eigenform of level $\Gamma_1(N)$, with its nebentype character, and fix a complex embedding of its algebraic coefficients. For every positive integer $d$, there is a primitive Dirichlet character $\eta$ such that
--
--   $$\operatorname{ord}(\eta)=2,\qquad (\operatorname{cond}\eta,Nd)=1,\qquad L(f,\eta,k/2)\ne0.$$
--
--   Either parity of $\eta$ is allowed. In particular, this statement does not prescribe a local sign incompatible with the functional equation. It supplies the quadratic seed for odd-prime horizontal propagation, using the modular-symbol sign matching the chosen seed.
--
--   The result includes normalized eigenforms at nonminimal level: passing to the underlying primitive newform introduces only finitely many local Euler factors, which are nonzero at the center for twists of conductor coprime to $N$.
--
--   **Formalization Note.** The conclusion uses the mission's Mellin-integral critical value at index $k/2-1$. For quadratic characters its inverse-twist convention agrees with the usual quadratic twist. The statement does not use the mission's weight-two-specific `IsNewEigenform` predicate.
-- source:
--   Friedberg–Hoffstein, Nonvanishing theorems for automorphic L-functions on GL(2), Ann. of Math. 142 (1995), 385–423, https://doi.org/10.2307/2118638; prescribed-local-type formulation restated in Anandavardhanan–Prasad, A local-global question in automorphic forms, Compositio Math. 149 (2013), Theorem 10.6, p.986, https://www.math.iitb.ac.in/~dprasad/comp2013.pdf. The finite conductor avoidance is obtained by choosing a root-number-compatible quadratic local type with unrestricted parity. The general-nebentype twist functional equation is given by Bettin et al., A conjectural extension of Hecke's converse theorem, Lemma 4.10, https://arxiv.org/pdf/1704.02570. Extension from primitive newforms to simultaneous Hecke/U eigenforms uses standard oldform Euler factors and Ramanujan–Petersson bounds; that bridge is part of this open theorem. This corrects the seed parity restriction used in Kriz–Nordentoft Corollary 5.17, https://arxiv.org/html/2310.20678v3#S5.SS4.

import Definitions.Def_KN_HorizontalPadicL

set_option autoImplicit false

namespace HorizontalPadicL

/-- Friedberg--Hoffstein nonvanishing with finite conductor avoidance, allowing
either parity of the primitive quadratic character. -/
theorem friedberg_hoffstein_quadratic_twist_nonzero_anyParity_v2
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (heven : Even k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (d : ℕ) (hd : 0 < d) :
    ∃ η : DirichletCharacterWithLevel,
      η.2.IsPrimitive ∧
      orderOf η.2 = 2 ∧
      Nat.Coprime (N * d) η.2.conductor ∧
      @MTT.criticalLValue ι f.form
        η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2 (k / 2 - 1) ≠ 0 := by sorry

end HorizontalPadicL
