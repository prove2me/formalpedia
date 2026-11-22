-- Prove2me | Theorems.Thm_MasulloGRH_heckeLFunction_no_zero_re_ge_one
-- name    : MasulloGRH.heckeLFunction_no_zero_re_ge_one
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-21T15:10:00.240081+00:00
-- url     : https://prove2.me/theorems/4097fa76-f445-47f5-920e-ef638f3476cd
-- title:
--   $L_f(s,\chi)$ has no zeros on $\operatorname{Re}(s)\ge 1$
-- statement:
--   Let $F$ be a number field and let $\chi\colon C_F\to U(1)$ be a Hecke character, i.e. a continuous character of the idele class group $C_F=\mathrm{GL}_1(\mathbb A_F)/F^\times$. Write $L_f(s,\chi)$ for the finite Hecke $L$-function: the meromorphic continuation to $\mathbb C$ of the Euler product
--
--   $$L_f(s,\chi)=\prod_{v}\bigl(1-\chi(\mathfrak p_v)N(\mathfrak p_v)^{-s}\bigr)^{-1},\qquad \operatorname{Re}(s)>1,$$
--
--   taken over the finite places $v$, with $\chi(\mathfrak p_v)=0$ when $\chi$ is ramified at $v$.
--
--   $L_f(s,\chi)$ has no zero in the closed half-plane
--
--   $$\operatorname{Re}(s)\ge1 .$$
--
--   On the line $\operatorname{Re}(s)=1$ this is the non-vanishing of $L_f(1+it,\chi)$ for every real $t$; it contains $L_f(1,\chi)\neq0$ for a quadratic character $\chi$, which is the assertion $\sigma<1$ for the possible exceptional real zero in Proposition B.6.1.1. Combined with the zero-free region at large ordinates, it yields the zero-free region $\sigma>1-c/\log(|t|+3)$ at every height.
--
--   **Formalization Note** $L_f(s,\chi)$ is `heckeLFunction χ`, the continuation in normal form. As in Theorem B.6.1.3, "no zero" is expressed as `meromorphicOrderAt (heckeLFunction χ) s ≤ 0`, which allows the pole at $s=1+it_0$ when $\chi=|\cdot|_F^{-it_0}$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix B, §B.6.1.1, Proposition B.6.1.1 (Classical zero-free region for L_f(s,χ)), eq. (B.6.1.1), p. 636; the source deduces it from H. Iwaniec and E. Kowalski, Analytic Number Theory, §5.4, Theorem 5.10, p. 106.

import Definitions.Def_MasulloGRH_HeckeLFunction

set_option autoImplicit false

namespace MasulloGRH

theorem heckeLFunction_no_zero_re_ge_one
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) :
    ∀ s : ℂ, 1 ≤ s.re → meromorphicOrderAt (heckeLFunction χ) s ≤ 0 := by sorry

end MasulloGRH
