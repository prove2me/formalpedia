-- Prove2me | Theorems.Thm_MassartDKW_Tight_proposition_1
-- name    : MassartDKW.Tight.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:12:12.948556+00:00
-- url     : https://prove2.me/theorems/9ee5470d-bd1d-42ff-821f-796e2cebbd20
-- title:
--   Proposition 1 (2.5), p. 1272 — p_{λ,n}(j) ≤ n⁻¹(1 − ε/3s′ + ε²/6s′²) exp(0.4/ns − ε²(vₙ(s) + vₙ(s′))/24n) f_λ(s)
-- statement:
--   Let $n\ge1$, $\lambda>0$, $\varepsilon=\lambda/\sqrt n$, and let $j$ be an integer with $0\le j<n-\lambda\sqrt n$. Let $s=2\varepsilon/3+j/n$ and $s'=1-s$. If $n\varepsilon\ge2$, then
--   $$p_{\lambda,n}(j)\le\frac1n\Bigl(1-\frac{\varepsilon}{3s'}+\frac{\varepsilon^2}{6s'^2}\Bigr)\exp\Bigl(\frac{0.4}{ns}-\frac{\varepsilon^2}{24n}\bigl(v_n(s)+v_n(s')\bigr)\Bigr)f_\lambda(s),$$
--   where $v_n(s)=\bigl(s(s^2-1/(4n^2))\bigr)^{-1}$, $p_{\lambda,n}$ is Smirnov's point probability (2.1) and $f_\lambda$ is Csáki's density (2.2).
--
--   This is the key local comparison between the exact law of the crossing time of $-Z_n$ and that of the Brownian bridge; summing it over $j$ yields (2.11).
--
--   **Formalization Note** The statement is purely analytic: $p_{\lambda,n}(j)$ and $f_\lambda$ are the closed forms (2.1) and (2.2). `l` stands for $\lambda$; $\varepsilon$, $s$, $s'$ are local abbreviations.
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), p. 1272, Proposition 1, (2.5)

import Mathlib
import Definitions.Def_MassartDKW_Tight_Analytic

namespace MassartDKW.Tight

theorem proposition_1 (n : ℕ) (hn : 1 ≤ n) (l : ℝ) (hl : 0 < l) (j : ℕ)
    (hj : (j : ℝ) < n - l * Real.sqrt n) (hnε : 2 ≤ (n : ℝ) * (l / Real.sqrt n)) :
    let ε := l / Real.sqrt n
    let s := 2 * ε / 3 + (j : ℝ) / n
    let s' := 1 - s
    smirnovP l n j ≤ (1 / (n : ℝ)) * (1 - ε / (3 * s') + ε ^ 2 / (6 * s' ^ 2)) *
      Real.exp (0.4 / ((n : ℝ) * s) - ε ^ 2 / (24 * (n : ℝ)) * (v n s + v n s')) *
      csakiDensity l s := by sorry

end MassartDKW.Tight
