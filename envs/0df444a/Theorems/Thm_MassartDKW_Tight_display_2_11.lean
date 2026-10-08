-- Prove2me | Theorems.Thm_MassartDKW_Tight_display_2_11
-- name    : MassartDKW.Tight.display_2_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:13:29.79606+00:00
-- url     : https://prove2.me/theorems/69511314-3d35-4d2d-9707-4940bc4bda56
-- title:
--   (2.11), p. 1280 — (3√n/2λ)(exp(2λ²)P(Dₙ⁻ > λ) − 1) ≤ ηₙ(λ) for n ≥ 39, γn^{−1/6} ≤ λ ≤ √n/2
-- statement:
--   Let $n\ge39$ and $\gamma n^{-1/6}\le\lambda\le\sqrt n/2$ with $\gamma=1.0841$. With $\mu=0.4345$ and $C_{\lambda,n}=\exp(2\lambda^2)P(D_n^->\lambda)$,
--   $$\frac{3\sqrt n}{2\lambda}\bigl(C_{\lambda,n}-1\bigr)\le-1+\Bigl(\lambda+\frac1{4\lambda}+\frac{3\mu}\lambda+\frac{3\mu}{2\lambda^3}\Bigr)n^{-1/2}-\frac\mu2\Bigl(4+\frac1{\lambda^2}\Bigr)n^{-1}+\frac\mu2\Bigl(4\lambda+\frac1\lambda\Bigr)n^{-3/2}.$$
--   The right side is denoted $\eta_n(\lambda)$.
--
--   This is a nonasymptotic form of Smirnov's expansion (1.3), obtained by summing Proposition 1 over $j$ with Lemmas 3 and 4. Combined with $\eta_n<0$ it proves Theorem 1 for $n\ge39$, $\lambda\le\sqrt n/2$.
--
--   **Formalization Note** $C_{\lambda,n}$ is the mission's `C n l`, which is $\exp(2\lambda^2)$ times Smirnov's exact sum (2.3), equal to $\exp(2\lambda^2)P(D_n^->\lambda)$ by the milestone for (2.3); the statement is thus free of probability. The hypotheses $n\ge39$ and $\gamma n^{-1/6}\le\lambda\le\sqrt n/2$ are those of the case of the proof in which (2.11) is derived ("Proof of Theorem 1 (where $n\ge39$ and $\lambda\le\sqrt n/2$)", p. 1279). The display just before (2.11) prints the coefficient $2\mu/(3n)$ in front of $I_{2,1}(\lambda)$; the expansion that yields (2.11) needs $\varepsilon\mu/(3n)$. The statement here is (2.11) itself, unaffected. `l` stands for $\lambda$.
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), p. 1280, (2.11) (proof of Theorem 1, case n ≥ 39 and λ ≤ √n/2, p. 1279)

import Mathlib
import Definitions.Def_MassartDKW_Tight_Analytic

namespace MassartDKW.Tight

theorem display_2_11 (n : ℕ) (hn : 39 ≤ n) (l : ℝ)
    (hl1 : 1.0841 * (n : ℝ) ^ (-(1 / 6 : ℝ)) ≤ l) (hl2 : l ≤ Real.sqrt n / 2) :
    3 * Real.sqrt n / (2 * l) * (C n l - 1) ≤ eta n l := by sorry

end MassartDKW.Tight
