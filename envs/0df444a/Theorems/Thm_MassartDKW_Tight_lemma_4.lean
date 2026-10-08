-- Prove2me | Theorems.Thm_MassartDKW_Tight_lemma_4
-- name    : MassartDKW.Tight.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:12:55.198981+00:00
-- url     : https://prove2.me/theorems/d2089810-4801-4db5-858d-bcdb3783e676
-- title:
--   Lemma 4, p. 1279 — I_{1,1}/2 = I_{1,0} = 1, I_{2,2}/2 = I_{2,1} = 4 + λ⁻², I_{2,0} = 2 + λ⁻²
-- statement:
--   For nonnegative $a,b$ and positive $\lambda$ let
--   $$I_{a,b}(\lambda)=\frac{\lambda\exp(2\lambda^2)}{\sqrt{2\pi}}\int_0^1u^{-1/2-a}(1-u)^{-1/2-b}\exp\Bigl(-\frac{\lambda^2}{2u(1-u)}\Bigr)du.$$
--   Then for every $\lambda>0$:
--
--   1. $I_{1,1}(\lambda)/2=I_{1,0}(\lambda)=1$;
--   2. $I_{2,2}(\lambda)/2=I_{2,1}(\lambda)=4+\lambda^{-2}$;
--   3. $I_{2,0}(\lambda)=2+\lambda^{-2}$.
--
--   These closed forms evaluate the integrals that appear when the bound of Proposition 1, after Lemma 3, is summed over $j$; they turn that sum into the explicit right side $\eta_n(\lambda)$ of (2.11).
--
--   **Formalization Note** The statement is the five equalities at the indices actually used. The integrals converge for every $a,b$ (the exponential factor kills the endpoint singularities), so the interval integral is the genuine one. $\lambda^{-2}$ is written $1/\lambda^2$; `l` stands for $\lambda$.
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), p. 1279, Lemma 4

import Mathlib
import Definitions.Def_MassartDKW_Tight_Analytic

namespace MassartDKW.Tight

theorem lemma_4 (l : ℝ) (hl : 0 < l) :
    I 1 1 l / 2 = 1 ∧ I 1 0 l = 1 ∧ I 2 2 l / 2 = 4 + 1 / l ^ 2 ∧ I 2 1 l = 4 + 1 / l ^ 2 ∧
      I 2 0 l = 2 + 1 / l ^ 2 := by sorry

end MassartDKW.Tight
