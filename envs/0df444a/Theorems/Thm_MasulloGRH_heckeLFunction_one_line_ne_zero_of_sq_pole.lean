-- Prove2me | Theorems.Thm_MasulloGRH_heckeLFunction_one_line_ne_zero_of_sq_pole
-- name    : MasulloGRH.heckeLFunction_one_line_ne_zero_of_sq_pole
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-21T15:15:39.449778+00:00
-- url     : https://prove2.me/theorems/4833ae58-2732-4e3a-9980-79c29db50fc2
-- title:
--   $L_f(1+it,\chi)\neq0$ when $L_f(s,\chi^2)$ has a pole at $1+2it$ (quadratic case)
-- statement:
--   Let $F$ be a number field and let $\chi\colon C_F\to U(1)$ be a Hecke character, i.e. a continuous character of the idele class group $C_F=\mathrm{GL}_1(\mathbb A_F)/F^\times$. Write $L_f(s,\chi)$ for the finite Hecke $L$-function, the meromorphic continuation of $\prod_v(1-\chi(\mathfrak p_v)N(\mathfrak p_v)^{-s})^{-1}$ from $\operatorname{Re}(s)>1$, and $\chi^2$ for the square of $\chi$ in the group of Hecke characters. Let $t$ be real.
--
--   If $L_f(s,\chi^2)$ has a pole at $s=1+2it$, then $L_f(s,\chi)$ has no zero at $s=1+it$:
--
--   $$
--   \operatorname{ord}_{s=1+2it}L_f(s,\chi^2)<0\quad\Longrightarrow\quad L_f(1+it,\chi)\neq0 .
--   $$
--
--   A pole of $L_f(s,\chi^2)$ on the line $\operatorname{Re}(s)=1$ occurs exactly when $\chi^2=|\cdot|_F^{-2it}$. Then $\psi=\chi|\cdot|_F^{it}$ satisfies $\psi^2=1$ and $L_f(s,\chi)=L_f(s-it,\psi)$, so the statement is the classical non-vanishing $L_f(1,\psi)\neq0$ for a Hecke character of order at most two. In Proposition B.6.1.1 it is the assertion that the possible exceptional real zero of a quadratic character satisfies $\sigma<1$. It is the one case of the non-vanishing of $L_f(s,\chi)$ on $\operatorname{Re}(s)=1$ that the inequality $|\zeta_F(\sigma)^3L(\sigma+it,\chi)^4L(\sigma+2it,\chi^2)|\ge1$ of (B.6.1.23) does not settle.
--
--   **Formalization Note** $L_f(s,\chi)$ is `heckeLFunction χ`, the continuation in normal form, and $\chi^2$ is `χ * χ` in the Pontryagin dual. "Pole" is negative meromorphic order; "no zero" is `meromorphicOrderAt (heckeLFunction χ) (1 + t * I) ≤ 0`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix B, §B.6.1.1, Proposition B.6.1.1, p. 636 (the exceptional real zero of a quadratic character satisfies σ < 1), with the inequality (B.6.1.23), p. 640; the source cites H. Iwaniec and E. Kowalski, Analytic Number Theory, §5.4, Theorem 5.10, p. 106.

import Definitions.Def_MasulloGRH_HeckeLFunction

set_option autoImplicit false

namespace MasulloGRH

theorem heckeLFunction_one_line_ne_zero_of_sq_pole
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) (t : ℝ)
    (hpole : meromorphicOrderAt (heckeLFunction (χ * χ)) (1 + ((2 * t : ℝ) : ℂ) * Complex.I) < 0) :
    meromorphicOrderAt (heckeLFunction χ) (1 + (t : ℂ) * Complex.I) ≤ 0 := by sorry

end MasulloGRH
