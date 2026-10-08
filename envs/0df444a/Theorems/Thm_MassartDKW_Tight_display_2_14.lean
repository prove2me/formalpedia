-- Prove2me | Theorems.Thm_MassartDKW_Tight_display_2_14
-- name    : MassartDKW.Tight.display_2_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:13:16.806074+00:00
-- url     : https://prove2.me/theorems/f09531d0-a4a4-4415-b7c7-0b72d9382e13
-- title:
--   (2.14), p. 1282 — C_{λ,n} ≤ λ√n + p_{λ,n}(0) exp(2λ²)
-- statement:
--   Let $n\ge2$ and $0<\lambda<\sqrt n$. With $C_{\lambda,n}=\exp(2\lambda^2)P(D_n^->\lambda)$ and $p_{\lambda,n}(0)=(1-\lambda/\sqrt n)^n$,
--   $$C_{\lambda,n}\le\lambda\sqrt n+p_{\lambda,n}(0)\exp(2\lambda^2).$$
--
--   This crude bound, derived from Lemma 1 and Proposition 2(ii), is used for $n\le13$ in the proof of Proposition 2(iii).
--
--   **Formalization Note** The hypotheses $n\ge2$ and $0<\lambda<\sqrt n$ are those of Proposition 2, inside whose proof (2.14) is derived. For $\lambda\ge\sqrt n$ the inequality can fail ($n=1$, $\lambda=2$: the left side is $0$, the right side $2-e^8$), so the restriction is necessary. $C_{\lambda,n}$ is `C n l`, defined through (2.3); `l` stands for $\lambda$.
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), p. 1282, (2.14) (proof of Proposition 2(iii))

import Mathlib
import Definitions.Def_MassartDKW_Tight_Analytic

namespace MassartDKW.Tight

theorem display_2_14 (n : ℕ) (hn : 2 ≤ n) (l : ℝ) (hl0 : 0 < l) (hl : l < Real.sqrt n) :
    C n l ≤ l * Real.sqrt n + smirnovP l n 0 * Real.exp (2 * l ^ 2) := by sorry

end MassartDKW.Tight
