-- Prove2me | Theorems.Thm_MassartDKW_Tight_display_2_13
-- name    : MassartDKW.Tight.display_2_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:13:54.593636+00:00
-- url     : https://prove2.me/theorems/98c97729-dbd6-4645-83ac-6684ac2e7bee
-- title:
--   (2.13), p. 1282 — C_{λ,n} ≤ exp((8/n) ∨ 0.3) for n ≥ 4 and λ > 0
-- statement:
--   For every integer $n\ge4$ and every $\lambda>0$, with $C_{\lambda,n}=\exp(2\lambda^2)P(D_n^->\lambda)$,
--   $$C_{\lambda,n}\le\exp\Bigl(\frac8n\vee0.3\Bigr).$$
--
--   This crude uniform bound is used for $n\ge14$ in the proof of Proposition 2(iii).
--
--   **Formalization Note** $\vee$ is the maximum. $C_{\lambda,n}$ is `C n l`, defined through the exact formula (2.3); for $\lambda\ge\sqrt n$ it is $0$ and the bound holds trivially, as the page's "any positive $\lambda$" requires. `l` stands for $\lambda$.
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), p. 1282, (2.13)

import Mathlib
import Definitions.Def_MassartDKW_Tight_Analytic

namespace MassartDKW.Tight

theorem display_2_13 (n : ℕ) (hn : 4 ≤ n) (l : ℝ) (hl : 0 < l) :
    C n l ≤ Real.exp (max (8 / (n : ℝ)) 0.3) := by sorry

end MassartDKW.Tight
