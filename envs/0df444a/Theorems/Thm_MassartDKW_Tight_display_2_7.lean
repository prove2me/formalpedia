-- Prove2me | Theorems.Thm_MassartDKW_Tight_display_2_7
-- name    : MassartDKW.Tight.display_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:58:09.358508+00:00
-- url     : https://prove2.me/theorems/f2df5f60-e52c-4a0b-b409-93dbe2d2db0d
-- title:
--   (2.7), p. 1274 — p_{λ,n}(j) ≤ n⁻¹(1 + 2ε/3s′)^{−1/2} C_j exp(−nεφ(t)/t + ψ(t)) f_λ(s) for j ≥ 1
-- statement:
--   Let $n\ge1$, $\lambda>0$, $\varepsilon=\lambda/\sqrt n$, and let $j$ be an integer with $1\le j<n-\lambda\sqrt n$. Put $s=2\varepsilon/3+j/n$, $s'=1-s$, $t=\varepsilon/(s-2\varepsilon/3)$ $(=n\varepsilon/j)$ and $C_j=\exp(-1/(12j+1))$. Then
--   $$p_{\lambda,n}(j)\le\frac1n\Bigl(1+\frac{2\varepsilon}{3s'}\Bigr)^{-1/2}C_j\exp\Bigl(-\frac{n\varepsilon\varphi(t)}{t}+\psi(t)\Bigr)f_\lambda(s),$$
--   with $\varphi$ from Lemma 1 and $\psi$ from (2.6).
--
--   This is the intermediate bound in the proof of Proposition 1 for $j\ge1$, obtained from Stirling's formula with upper and lower bounds and Lemma 1(ii); the error term $-n\varepsilon\varphi(t)/t+\psi(t)$ is then controlled by Lemma 2.
--
--   **Formalization Note** The hypothesis $n\varepsilon\ge2$ of Proposition 1 is not used in the derivation of (2.7) and is not assumed. `l` stands for $\lambda$.
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), p. 1274, (2.7) (proof of Proposition 1, case j ≥ 1; C_j defined on p. 1273)

import Mathlib
import Definitions.Def_MassartDKW_Tight_Analytic

namespace MassartDKW.Tight

theorem display_2_7 (n : ℕ) (hn : 1 ≤ n) (l : ℝ) (hl : 0 < l) (j : ℕ) (hj1 : 1 ≤ j)
    (hj : (j : ℝ) < n - l * Real.sqrt n) :
    let ε := l / Real.sqrt n
    let s := 2 * ε / 3 + (j : ℝ) / n
    let s' := 1 - s
    let t := ε / (s - 2 * ε / 3)
    smirnovP l n j ≤ (1 / (n : ℝ)) * (1 + 2 * ε / (3 * s')) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-1 / (12 * (j : ℝ) + 1)) * Real.exp (-((n : ℝ) * ε * phi t / t) + psi t) *
      csakiDensity l s := by sorry

end MassartDKW.Tight
