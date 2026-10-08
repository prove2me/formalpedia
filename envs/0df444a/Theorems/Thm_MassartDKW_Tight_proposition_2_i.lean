-- Prove2me | Theorems.Thm_MassartDKW_Tight_proposition_2_i
-- name    : MassartDKW.Tight.proposition_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:13:09.653395+00:00
-- url     : https://prove2.me/theorems/22ac79d6-d22e-43c9-9f6f-6c4d9873aaf0
-- title:
--   Proposition 2(i), p. 1281 — λ ↦ C_{λ,n} is nonincreasing on [√n/2, √n), n ≥ 2
-- statement:
--   Let $n\ge2$ and $C_{\lambda,n}=\exp(2\lambda^2)P(D_n^->\lambda)$. Then $\lambda\mapsto C_{\lambda,n}$ is nonincreasing on $[\sqrt n/2,\sqrt n)$: for $\sqrt n/2\le\lambda_1\le\lambda_2<\sqrt n$,
--   $$C_{\lambda_2,n}\le C_{\lambda_1,n}.$$
--
--   This reduces Theorem 1 for $\lambda>\sqrt n/2$ to the value at $\lambda=\sqrt n/2$, which is covered by the case $n\ge39$, $\lambda\le\sqrt n/2$ or by the numerical check for $n\le38$.
--
--   **Formalization Note** The page prints "$\frac{d}{d\lambda}C_{\lambda,n}\ge0$". The proof shows that $\frac{d}{d\lambda}\log(e^{2\lambda^2}p_{\lambda,n}(j))<0$ for every $j$, and the final step (p. 1282) uses $C_{\lambda,n}\le C_{\sqrt n/2,n}$; the intended statement is that $C$ is nonincreasing, which is what is stated. It is stated as monotonicity rather than as a sign of the derivative, since $C_{\lambda,n}$ has kinks where $n-\lambda\sqrt n$ crosses an integer and Mathlib's derivative is $0$ at a non-differentiable point. $C_{\lambda,n}$ is `C n l`, defined through the exact formula (2.3).
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), p. 1281, Proposition 2(i) (C_{λ,n} defined on p. 1281)

import Mathlib
import Definitions.Def_MassartDKW_Tight_Analytic

namespace MassartDKW.Tight

theorem proposition_2_i (n : ℕ) (hn : 2 ≤ n) :
    AntitoneOn (C n) (Set.Ico (Real.sqrt n / 2) (Real.sqrt n)) := by sorry

end MassartDKW.Tight
