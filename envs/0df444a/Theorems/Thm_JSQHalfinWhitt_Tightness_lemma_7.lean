-- Prove2me | Theorems.Thm_JSQHalfinWhitt_Tightness_lemma_7
-- name    : JSQHalfinWhitt.Tightness.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:34.382145+00:00
-- url     : https://prove2.me/theorems/8366a51d-cb04-4c98-a179-a6b91f5929e6
-- title:
--   Lemma 7 — $f^*$ of (4.14) is well-defined, solves the PDE (3.7)–(3.8) and satisfies (3.9)–(3.11)
-- statement:
--   Let $n \ge 1$, $0 < \beta < \sqrt n$ and $\kappa > \beta$, and let $f^*$ be the function (4.14):
--   $$f^*(x) = \begin{cases} 0, & x_2 \in [0, \kappa/\sqrt n],\\ x_2 - \frac{\kappa}{\sqrt n} - \frac{\kappa}{\sqrt n}\log(\sqrt n x_2/\kappa), & x \le \Gamma^{(\kappa)} \text{ and } x_2 \ge \kappa/\sqrt n,\\ x_2(1 - e^{-\tau(x)}) - \frac{\kappa}{\sqrt n}\tau(x) + \frac12\frac{\sqrt n}{\beta}\big(x_2 e^{-\tau(x)} - \kappa/\sqrt n\big)^2, & x \ge \Gamma^{(\kappa)}. \end{cases}$$
--   Then:
--
--   1. $f^*$ is well-defined: on $\Omega$, the branches agree wherever two of the three regions overlap;
--   2. $f^*$ has partial derivatives $f^*_1, f^*_2$ on $\Omega$ (one-sided on $\partial\Omega$), with $f^*_1(\cdot, x_2)$ and $f^*_2(x_1, \cdot)$ absolutely continuous for all $x \in \Omega$;
--   3. $f^*$ satisfies the PDE
--   $$Lf^*(x) = -\big((x_2 - \kappa/\sqrt n)\vee 0\big),\ x \in \Omega,\qquad f^*_1(0, x_2) = f^*_2(0, x_2),\ x_2 \ge 0; \tag{3.7–3.8}$$
--   4. its second-order weak derivatives satisfy $f^*_{11}, f^*_{12}, f^*_{22} \ge 0$ on $\Omega$, $f^*_{11} = f^*_{22} = 0$ for $x_2 \in [0, \kappa/\sqrt n]$, and for $x_2 \ge \kappa/\sqrt n$
--   $$f^*_{11}(x) \le \frac{\sqrt n}{\beta}\Big(\frac{\kappa}{\kappa - \beta} + 1\Big),\qquad f^*_{22}(x) \le \frac{\sqrt n}{\beta}\Big(5 + \frac{2\kappa}{\kappa - \beta}\Big). \tag{3.9–3.11}$$
--
--   This is the proof of Lemma 4: the explicit function $f^*$, built from the fluid model, is the Lyapunov function whose derivative bounds drive the tightness estimate (3.18).
--
--   **Formalization Note** "Well-defined" is stated as three agreements on $\Omega$: the middle branch vanishes where $x_2 = \kappa/\sqrt n$ and $x \le \Gamma^{(\kappa)}$; the upper branch vanishes where $x_2 \le \kappa/\sqrt n$ and $x \ge \Gamma^{(\kappa)}$; the middle and upper branches agree on $\Gamma^{(\kappa)}$ where $x_2 \ge \kappa/\sqrt n$. The Lean `fStar` is an `if` cascade taking the first applicable branch. Items 2–4 use the predicates `IsWeakC2`, `HasWeakMixed`, `SolvesPDE`, `DerivBounds` of the PDE definition file, with the partial and weak derivatives named and asserted to be the derivatives of `fStar` (no junk derivatives). The references "(3.7)–(3.8)" and "(3.9)–(3.11)" of the printed statement are expanded in full.
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), p. 15, Lemma 7 (f^* in (4.14), p. 15; (3.7)–(3.11), p. 8)

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_PDE
import Definitions.Def_JSQHalfinWhitt_Tightness_Fluid

namespace JSQHalfinWhitt.Tightness

/-- Lemma 7 (Braverman, p. 15): for `κ > β`, the function `f^*` of (4.14) is well-defined (its
three branches agree where the regions `{x_2 ∈ [0, κ/√n]}`, `{x ≤ Γ^{(κ)}, x_2 ≥ κ/√n}` and
`{x ≥ Γ^{(κ)}}` overlap), has partial derivatives `f^*_1, f^*_2` on `Ω` with `f^*_1(·, x_2)`,
`f^*_2(x_1, ·)` absolutely continuous, solves the PDE (3.7)–(3.8), and its second-order weak
derivatives satisfy (3.9)–(3.11). -/
theorem lemma_7 (n : ℕ) (β κ : ℝ) (hn : 1 ≤ n) (hβ : 0 < β) (hβn : β < Real.sqrt n)
    (hκ : β < κ) :
    (∀ x ∈ Omega, x.2 = κ / Real.sqrt n → x.2 ≤ nuStar β κ n x.1 → fStarMid κ n x = 0) ∧
    (∀ x ∈ Omega, x.2 ≤ κ / Real.sqrt n → nuStar β κ n x.1 ≤ x.2 → fStarUpper β κ n x = 0) ∧
    (∀ x ∈ Omega, κ / Real.sqrt n ≤ x.2 → x.2 = nuStar β κ n x.1 →
        fStarMid κ n x = fStarUpper β κ n x) ∧
    ∃ f1 f2 f11 f12 f22 : ℝ × ℝ → ℝ,
      IsWeakC2 (fStar β κ n) f1 f2 f11 f22 ∧ HasWeakMixed f1 f12 ∧ SolvesPDE β κ n f1 f2 ∧
        DerivBounds β κ n f11 f12 f22 := by sorry

end JSQHalfinWhitt.Tightness
