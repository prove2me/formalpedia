-- Prove2me | Theorems.Thm_MasulloGRH_heckeLFunction_convexity_bound
-- name    : MasulloGRH.heckeLFunction_convexity_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T03:40:45.90055+00:00
-- url     : https://prove2.me/theorems/f4928c3e-efd3-4380-ae48-d586261a6025
-- title:
--   Proposition B.1.1.3 — convexity bound for $L_f(s,\chi)$
-- statement:
--   Let $F$ be a number field and let $\chi\colon C_F\to U(1)$ be a Hecke character, i.e. a continuous character of the idele class group $C_F=\mathrm{GL}_1(\mathbb A_F)/F^\times$. Write $L_f(s,\chi)$ for the finite Hecke $L$-function: the meromorphic continuation to $\mathbb C$ of the Euler product $\prod_{v}(1-\chi(\mathfrak p_v)N(\mathfrak p_v)^{-s})^{-1}$ over the finite places at which $\chi$ is unramified, which converges for $\operatorname{Re}(s)>1$.
--
--   For every $\varepsilon>0$ there are real numbers $C$ and $T$ such that
--
--   $$|L_f(\sigma+it,\chi)|\le C\,|t|^{[F:\mathbb Q]\frac{1-\sigma}{2}+\varepsilon}\qquad\text{for all }\sigma\in[0,1]\text{ and all real } t \text{ with } |t|\ge T .$$
--
--   This is the convexity bound in the $t$-aspect. It is the growth estimate in the critical strip that the later contour arguments of the draft use.
--
--   **Formalization Note** The source says that the implied constant does not depend on $\varepsilon$. Since the threshold $T$ may depend on $\varepsilon$, that form and the form stated here are equivalent: a bound with exponent $\varepsilon/2$ and constant $C$ gives a bound with exponent $\varepsilon$ and constant $1$ once $|t|^{\varepsilon/2}\ge C$. The function $L_f(s,\chi)$ is represented by `heckeLFunction χ`, the continuation in normal form, which takes the value $0$ at a pole.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix B, §B.1, Proposition B.1.1.3 (Convexity Bound), eq. (B.1.1.12), p. 591

import Definitions.Def_MasulloGRH_HeckeLFunction

set_option autoImplicit false

namespace MasulloGRH

theorem heckeLFunction_convexity_bound
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) (ε : ℝ) (hε : 0 < ε) :
    ∃ C T : ℝ, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → T ≤ |s.im| →
      ‖heckeLFunction χ s‖ ≤
        C * |s.im| ^ ((Module.finrank ℚ F : ℝ) * ((1 - s.re) / 2) + ε) := by sorry

end MasulloGRH
