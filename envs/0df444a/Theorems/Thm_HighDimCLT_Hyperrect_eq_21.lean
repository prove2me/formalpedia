-- Prove2me | Theorems.Thm_HighDimCLT_Hyperrect_eq_21
-- name    : HighDimCLT.Hyperrect.eq_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:38:44.11106+00:00
-- url     : https://prove2.me/theorems/42dd03c5-caec-433e-a6cb-0caaa2b00060
-- title:
--   (21), App. B, p. 2325 — 0 ≤ F_β(w) − max_j(w_j − y_j) ≤ β⁻¹ log p = φ⁻¹ for β = φ log p
-- statement:
--   Let $p \ge 3$, $\phi \ge 1$ and $y \in \mathbb R^p$, and put $\beta := \phi\log p$. Let $F_\beta(w) = \beta^{-1}\log\sum_{j=1}^p \exp(\beta(w_j - y_j))$ be the smooth maximum. Then for every $w \in \mathbb R^p$,
--
--   $$0 \le F_\beta(w) - \max_{1\le j\le p}(w_j - y_j) \le \beta^{-1}\log p = \phi^{-1}.$$
--
--   The smooth maximum $F_\beta$ approximates the maximum coordinate of $w - y$ within $\phi^{-1}$, which is what lets the proof of Lemma 5.1 replace the indicator of $\{w \le y\}$ by a smooth function of $w$.
--
--   **Formalization Note** The maximum is the finite supremum over $j \in \{1,\dots,p\}$; with $p \ge 3$ the logarithm $\log p$ is positive, so $\beta > 0$.
-- source:
--   Chernozhukov, Chetverikov and Kato, Central limit theorems and bootstrap in high dimensions, Ann. Probab. 45 (2017), p. 2325, App. B, display (21)

import Mathlib
import Definitions.Def_HighDimCLT_Hyperrect_Setting

open MeasureTheory ProbabilityTheory

namespace HighDimCLT.Hyperrect

theorem eq_21 (p : ℕ) (hp : 3 ≤ p) (φ : ℝ) (hφ : 1 ≤ φ) (y w : E p) :
    0 ≤ Fβ (φ * Real.log p) y w - (⨆ j : Fin p, (w j - y j)) ∧
    Fβ (φ * Real.log p) y w - (⨆ j : Fin p, (w j - y j)) ≤ (φ * Real.log p)⁻¹ * Real.log p ∧
    (φ * Real.log p)⁻¹ * Real.log p = φ⁻¹ := by sorry

end HighDimCLT.Hyperrect
