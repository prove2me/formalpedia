-- Prove2me | Theorems.Thm_JSQHalfinWhitt_Tightness_lemma_4
-- name    : JSQHalfinWhitt.Tightness.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:36.212532+00:00
-- url     : https://prove2.me/theorems/2304c8ee-6c13-4de0-a93b-770ed4954df3
-- title:
--   Lemma 4 — the PDE (3.7)–(3.8) has a solution $f^*$ with weak second derivatives bounded as in (3.9)–(3.11)
-- statement:
--   Let $n \ge 1$, $0 < \beta < \sqrt n$, let $Lf(x) = (-x_1 + x_2 - \beta/\sqrt n)f_1(x) - x_2 f_2(x)$ be as in (3.4), and fix $\kappa > \beta$. The PDE
--   $$Lf(x) = -\big((x_2 - \kappa/\sqrt n)\vee 0\big),\quad x \in \Omega, \tag{3.7}$$
--   $$f_1(0, x_2) = f_2(0, x_2),\quad x_2 \ge 0 \tag{3.8}$$
--   has a solution $f^*$ with $f^*_1(\cdot, x_2)$, $f^*_2(x_1, \cdot)$ absolutely continuous for all $x \in \Omega$, whose second-order weak derivatives satisfy
--   $$f^*_{11}(x), f^*_{12}(x), f^*_{22}(x) \ge 0,\quad x \in \Omega, \tag{3.9}$$
--   $$f^*_{11}(x) = f^*_{22}(x) = 0,\quad x_2 \in [0, \kappa/\sqrt n], \tag{3.10}$$
--   $$f^*_{11}(x) \le \frac{\sqrt n}{\beta}\Big(\frac{\kappa}{\kappa - \beta} + 1\Big),\quad f^*_{22}(x) \le \frac{\sqrt n}{\beta}\Big(5 + \frac{2\kappa}{\kappa - \beta}\Big),\quad x_2 \ge \kappa/\sqrt n. \tag{3.11}$$
--
--   $f^*$ is the Lyapunov function of the generator comparison argument: the PDE removes the drift and the reflection term from the generator expansion of Lemma 3, and the derivative bounds control the remainder $\varepsilon$.
--
--   **Formalization Note** The statement asserts the existence of $f^*$ together with named functions $f^*_1, f^*_2$ (its one-sided partial derivatives on $\Omega$) and $f^*_{11}, f^*_{12}, f^*_{22}$ (its weak second derivatives, in the literal form of a.e. derivatives of absolutely continuous functions on compact intervals of each line). A "solution" is thereby required to have genuine partial derivatives; junk values of a derivative operator cannot satisfy (3.7). The constants are exactly the paper's.
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), p. 8, Lemma 4, (3.7)–(3.11)

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_PDE

namespace JSQHalfinWhitt.Tightness

/-- Lemma 4 (Braverman, p. 8): for `κ > β`, the PDE (3.7)–(3.8) has a solution `f^*` with
`f^*_1(·, x_2)`, `f^*_2(x_1, ·)` absolutely continuous on `Ω` whose second-order weak derivatives
satisfy (3.9)–(3.11). The partial derivatives are named (`f1`, `f2`, …) and asserted to be the
one-sided partial derivatives and weak derivatives of `f`, so the PDE is not about junk values. -/
theorem lemma_4 (n : ℕ) (β κ : ℝ) (hn : 1 ≤ n) (hβ : 0 < β) (hβn : β < Real.sqrt n)
    (hκ : β < κ) :
    ∃ f f1 f2 f11 f12 f22 : ℝ × ℝ → ℝ,
      IsWeakC2 f f1 f2 f11 f22 ∧ HasWeakMixed f1 f12 ∧ SolvesPDE β κ n f1 f2 ∧
        DerivBounds β κ n f11 f12 f22 := by sorry

end JSQHalfinWhitt.Tightness
