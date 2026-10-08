-- Prove2me | Theorems.Thm_GloriaOtto_Variance_lemma_2_8
-- name    : GloriaOtto.Variance.lemma_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:20.50004+00:00
-- url     : https://prove2.me/theorems/0fd0f5c1-8a9f-4414-9945-005f8c51baaf
-- title:
--   Lemma 2.8 (i), (iii) — BMO/L^q bounds and decay of the Green's function G_T on dyadic annuli
-- statement:
--   Let $d \ge 2$, $0 < \alpha \le \beta$. For all exponents $q \ge 1$ and $r \ge 0$ there are constants $C$ and $R_0$, depending only on $d, \alpha, \beta, q, r$, such that for every $a \in \mathcal A_{\alpha\beta}$, every $T > 0$, every $y \in \mathbb Z^d$ and every $R \ge R_0$:
--
--   1. (2.20) if $d = 2$,
--   $$\sum_{|x-y|\le R}\big|G_T(x,y) - \bar G_T(\cdot,y)_{\{|x-y|\le R\}}\big|^q \le C R^2,$$
--   where $\bar G_T(\cdot,y)_{\{|x-y|\le R\}}$ is the average of $G_T(\cdot,y)$ over the ball $\{x\in\mathbb Z^d : |x-y|\le R\}$;
--   2. (2.21) if $d > 2$,
--   $$\sum_{R\le|x-y|\le 2R} |G_T(x,y)|^q \le C R^d (R^{2-d})^q;$$
--   3. (2.23) if moreover $R \ge \sqrt T$,
--   $$\sum_{R\le|x-y|\le 2R} |G_T(x,y)|^q \le C R^d (R^{2-d})^q (\sqrt T R^{-1})^r .$$
--
--   These are the averaged versions of the optimal decay $G_T(x,y) \lesssim |x-y|^{2-d}$ on dyadic annuli, with a BMO substitute in $d = 2$ and extra decay beyond the scale $\sqrt T$.
--
--   **Formalization Note.** "$R \gg 1$" is $R \ge R_0$. Part (iii) is printed "for all $R \ge \sqrt T$"; it is stated here for $R \ge \max(R_0, \sqrt T)$, because for small $T$ and large $r$ the bound fails at bounded $R$ (the paper uses it only for $R \gg 1$). $|G_T|^q$ is written with an absolute value; $G_T \ge 0$, so this is the paper's $G_T^q$. Part (ii), (2.22), is not formalized.
-- source:
--   Gloria, Otto, arXiv:1104.1291v1, Lemma 2.8 (i) and (iii), (2.20), (2.21), (2.23), pp. 18–19

import Mathlib
import Definitions.Def_GloriaOtto_Variance_Setup

open MeasureTheory ProbabilityTheory

namespace GloriaOtto.Variance

theorem lemma_2_8 (d : ℕ) (hd : 2 ≤ d) (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) :
    ∀ q r : ℝ, 1 ≤ q → 0 ≤ r → ∃ C R₀ : ℝ, ∀ a : Edge d → ℝ, InA α β a →
      ∀ T : ℝ, 0 < T → ∀ y : Site d, ∀ R : ℝ, R₀ ≤ R →
        (d = 2 →
          ∑' x, {x : Site d | latNorm (x - y) ≤ R}.indicator
              (fun x => |greenT a T x y - ballAvg (fun x' => greenT a T x' y) y R| ^ q) x
            ≤ C * R ^ 2) ∧
        (2 < d →
          ∑' x, {x : Site d | R ≤ latNorm (x - y) ∧ latNorm (x - y) ≤ 2 * R}.indicator
              (fun x => |greenT a T x y| ^ q) x
            ≤ C * R ^ (d : ℝ) * (R ^ (2 - (d : ℝ))) ^ q) ∧
        (Real.sqrt T ≤ R →
          ∑' x, {x : Site d | R ≤ latNorm (x - y) ∧ latNorm (x - y) ≤ 2 * R}.indicator
              (fun x => |greenT a T x y| ^ q) x
            ≤ C * R ^ (d : ℝ) * (R ^ (2 - (d : ℝ))) ^ q * (Real.sqrt T / R) ^ r) := by sorry

end GloriaOtto.Variance
