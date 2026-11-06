-- Prove2me | Theorems.Thm_GuthMaynard_Affine_lintegral_W_sq_III
-- name    : GuthMaynard.Affine.lintegral_W_sq_III
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T00:06:48.578141+00:00
-- url     : https://prove2.me/theorems/309fd2e2-cf76-44b0-a84c-1e95817403e0
-- title:
--   High frequencies in Guth–Maynard Lemma 9.2 — the integral of W(ξ)² over |ξ| > T²⁰ is O(M⁶(∫f)²)
-- statement:
--   Notation from the bundle `Def_GuthMaynardAffine` (`Wfun`, `Adm`, `Regime`). Let $C\ge1$, $c$ and $K>0$. Then there are $A\ge0$ and $T_1$ such that for every $T\ge T_1$, every $f$ with `Adm C c T f` and all $M,M_1,M_2,M_3$ with `Regime T M M₁ M₂ M₃`,
--
--   $$\int_{|\xi|>T^{20}}W(\xi)^2\,d\xi\le A\,M^6\Big(\int f\Big)^2,$$
--
--   where $W$ = `Wfun K M₁ M₂ M₃ f`.
--
--   A step in the proof of Guth–Maynard's Proposition 9.1 (Lemma 9.2 and its proof, arXiv:2405.20552v2 pp. 30–35); not a claim of the paper as stated.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), pp. 30–35, a step in the proof of Lemma 9.2 (used for Proposition 9.1)

import Mathlib
import Definitions.Def_GuthMaynard
import Definitions.Def_GuthMaynardAffine

namespace GuthMaynard.Affine

open GuthMaynard MeasureTheory FourierTransform
open scoped ENNReal

theorem lintegral_W_sq_III (C : ℝ) (c : ℕ → ℝ → ℝ) (K : ℝ) (hC : 1 ≤ C) (hK : 0 < K) :
    ∃ A T₁ : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T₁ ≤ T → ∀ f : ℝ → ℝ, Adm C c T f →
      ∀ M M₁ M₂ M₃ : ℝ, Regime T M M₁ M₂ M₃ →
        ∫⁻ ξ in {ξ : ℝ | T ^ 20 < |ξ|}, ENNReal.ofReal (Wfun K M₁ M₂ M₃ f ξ ^ 2) ≤
          ENNReal.ofReal (A * M ^ 6 * (∫ u, f u) ^ 2) := by
  sorry

end GuthMaynard.Affine
