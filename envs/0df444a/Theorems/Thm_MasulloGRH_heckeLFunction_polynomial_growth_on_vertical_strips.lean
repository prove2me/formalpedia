-- Prove2me | Theorems.Thm_MasulloGRH_heckeLFunction_polynomial_growth_on_vertical_strips
-- name    : MasulloGRH.heckeLFunction_polynomial_growth_on_vertical_strips
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T03:40:10.343882+00:00
-- url     : https://prove2.me/theorems/cc9b0a6f-7f4a-4448-be63-cab74440d701
-- title:
--   Lemma B.1.1.2 — polynomial growth of $L_f(s,\chi)$ in vertical strips
-- statement:
--   Let $F$ be a number field and let $\chi\colon C_F\to U(1)$ be a Hecke character, i.e. a continuous character of the idele class group $C_F=\mathrm{GL}_1(\mathbb A_F)/F^\times$. Write $L_f(s,\chi)$ for the finite Hecke $L$-function: the meromorphic continuation to $\mathbb C$ of the Euler product $\prod_{v}(1-\chi(\mathfrak p_v)N(\mathfrak p_v)^{-s})^{-1}$ over the finite places at which $\chi$ is unramified, which converges for $\operatorname{Re}(s)>1$.
--
--   For all real numbers $a<b$ there are real numbers $M>0$, $C$ and $T$ such that
--
--   $$|L_f(\sigma+it,\chi)|\le C\,|t|^{M}\qquad\text{for all }\sigma\in[a,b]\text{ and all real } t \text{ with } |t|\ge T .$$
--
--   The exponent $M$ may depend on $F$, $\chi$, $a$ and $b$. The bound makes the convexity exponent of $L_f(s,\chi)$ well defined on every vertical line.
--
--   **Formalization Note** The function $L_f(s,\chi)$ is represented by `heckeLFunction χ`, the continuation in normal form, which takes the value $0$ at a pole.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix B, §B.1, Lemma B.1.1.2, p. 590

import Definitions.Def_MasulloGRH_HeckeLFunction

set_option autoImplicit false

namespace MasulloGRH

theorem heckeLFunction_polynomial_growth_on_vertical_strips
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) (a b : ℝ) (hab : a < b) :
    ∃ M : ℝ, 0 < M ∧ ∃ C T : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ |s.im| →
      ‖heckeLFunction χ s‖ ≤ C * |s.im| ^ M := by sorry

end MasulloGRH
