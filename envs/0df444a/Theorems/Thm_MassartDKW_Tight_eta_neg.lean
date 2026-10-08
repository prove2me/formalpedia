-- Prove2me | Theorems.Thm_MassartDKW_Tight_eta_neg
-- name    : MassartDKW.Tight.eta_neg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:12:55.100077+00:00
-- url     : https://prove2.me/theorems/4a97d453-bca6-4276-833c-330c6227e657
-- title:
--   p. 1280 — ηₙ(λ) < 0 on [γn^{−1/6}, √n/2] for n ≥ 39 (a₃₉ ≤ −6·10⁻³, b₃₉ ≤ −0.4)
-- statement:
--   Let $\gamma=1.0841$, $\mu=0.4345$ and
--   $$\eta_n(\lambda)=-1+\Bigl(\lambda+\frac1{4\lambda}+\frac{3\mu}\lambda+\frac{3\mu}{2\lambda^3}\Bigr)n^{-1/2}-\frac\mu2\Bigl(4+\frac1{\lambda^2}\Bigr)n^{-1}+\frac\mu2\Bigl(4\lambda+\frac1\lambda\Bigr)n^{-3/2},$$
--   the right side of (2.11). For every integer $n\ge39$ and every $\lambda$ with $\gamma n^{-1/6}\le\lambda\le\sqrt n/2$,
--   $$\eta_n(\lambda)<0.$$
--
--   Together with (2.11) this gives $C_{\lambda,n}<1$, i.e. Theorem 1, in that range of $n$ and $\lambda$.
--
--   **Formalization Note** The paper argues via convexity of $\eta_n$ in $\lambda$ and monotonicity of the endpoint values $a_n=\eta_n(\gamma n^{-1/6})$, $b_n=\eta_n(\sqrt n/2)$ in $n$, with $a_{39}\le-6\times10^{-3}$ and $b_{39}\le-0.4$; the statement is the conclusion, negativity on the whole range. `l` stands for $\lambda$.
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), p. 1280, paragraph after (2.11)

import Mathlib
import Definitions.Def_MassartDKW_Tight_Analytic

namespace MassartDKW.Tight

theorem eta_neg (n : ℕ) (hn : 39 ≤ n) (l : ℝ)
    (hl1 : 1.0841 * (n : ℝ) ^ (-(1 / 6 : ℝ)) ≤ l) (hl2 : l ≤ Real.sqrt n / 2) :
    eta n l < 0 := by sorry

end MassartDKW.Tight
