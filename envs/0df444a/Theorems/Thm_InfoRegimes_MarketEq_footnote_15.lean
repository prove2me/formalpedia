-- Prove2me | Theorems.Thm_InfoRegimes_MarketEq_footnote_15
-- name    : InfoRegimes.MarketEq.footnote_15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:36.721993+00:00
-- url     : https://prove2.me/theorems/e7c57542-1331-49b0-addb-42968ab4f08a
-- title:
--   Footnote 15, p. 22 (special case f ≡ 0, λ ≡ 0 of Prop. 4.1) — self-consistency reduces to a quadratic in V_B with two positive roots under (27)
-- statement:
--   Assume the standing assumptions and write $d = \rho/(R-\rho)$.
--
--   1. At an information state $f = 0$ with $\lambda(f) = 0$ that the state process never leaves ($P(f_{t+1} = 0 \mid f_t = 0) = 1$), the self-consistency map sends the conjecture $V_B$ to
--   $$T(V_B)(0) = \Big(\frac{\gamma\big((1+d)^2\sigma_M^2 + V_B(0)\big)}{R}\Big)^2\sigma_X^2 .$$
--   2. A real number $V$ solves $V = \big(\gamma((1+d)^2\sigma_M^2 + V)/R\big)^2\sigma_X^2$ if and only if
--   $$V^2 + \Big[2(1+d)^2\sigma_M^2 - \frac{R^2}{\gamma^2\sigma_X^2}\Big]V + (1+d)^4\sigma_M^4 = 0 .$$
--   3. If $(1+d)\gamma\sigma_M\sigma_X \le 0.28$, this quadratic has exactly two real roots, and both are positive.
--
--   This is the paper's one-state version of condition (27): with no asymmetric information the model is an OLG model similar to Spiegel (1998), the self-consistent variance solves a quadratic, and its two roots correspond to a low-variance and a high-variance equilibrium. It is a special case of Proposition 4.1, not a step of its proof.
--
--   **Formalization Note.** $0.28$ is written as $7/25$.
-- source:
--   Glasserman, Mamaysky & Shen, Dynamic Information Regimes in Financial Markets, SSRN 3324789 (version of October 17, 2023), p. 22, footnote 15 (and the sentence it annotates)

import Mathlib
import Definitions.Def_InfoRegimes_MarketEq_Model

namespace InfoRegimes.MarketEq

theorem footnote_15 (P : Params) (hS : P.Standing) :
    (∀ (lam VB : State P → ℝ) (i : State P), grid P i = 0 → lam i = 0 → trans P lam i i = 1 →
        Tmap P lam VB i
          = (P.gam * ((1 + dConst P) ^ 2 * P.sigM ^ 2 + VB i) / P.R) ^ 2 * P.sigX ^ 2) ∧
      (∀ V : ℝ, V = (P.gam * ((1 + dConst P) ^ 2 * P.sigM ^ 2 + V) / P.R) ^ 2 * P.sigX ^ 2 ↔
        V ^ 2 + (2 * (1 + dConst P) ^ 2 * P.sigM ^ 2 - P.R ^ 2 / (P.gam ^ 2 * P.sigX ^ 2)) * V
          + (1 + dConst P) ^ 4 * P.sigM ^ 4 = 0) ∧
      ((1 + dConst P) * P.gam * P.sigM * P.sigX ≤ 7 / 25 →
        ∃ V₁ V₂ : ℝ, 0 < V₁ ∧ V₁ < V₂ ∧ ∀ V : ℝ,
          (V ^ 2 + (2 * (1 + dConst P) ^ 2 * P.sigM ^ 2 - P.R ^ 2 / (P.gam ^ 2 * P.sigX ^ 2)) * V
            + (1 + dConst P) ^ 4 * P.sigM ^ 4 = 0 ↔ V = V₁ ∨ V = V₂)) := by sorry

end InfoRegimes.MarketEq
