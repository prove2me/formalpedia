-- Prove2me | Theorems.Thm_OnlineBeckFiala_lemma_3_1
-- name    : OnlineBeckFiala.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:34:46.330576+00:00
-- url     : https://prove2.me/theorems/5db65471-04fd-430d-8732-f7082efa4db7
-- title:
--   Lemma 3.1 (Curvature of $u$) — tail (15) of $W(Y)$ and the second-difference bound (16)
-- statement:
--   Fix $\eta>0$, let $u$, $A$ be as in (12) and let $Y$ have density $Z^{-1}e^{-u}$ on $(-1,1)$. There are constants $M_\eta\ge1$ and $c_\eta,C_\eta>0$, depending only on $\eta$, such that $W(y)=M_\eta\,u(y)A(y)^{2+\eta}$ has the following two properties.
--
--   1. For every $x\ge1$,
--   $$P\{W(Y)>x\}\le C_\eta\exp\Bigl(-\frac{c_\eta x}{\log^{2+\eta}(ex)}\Bigr).\qquad(15)$$
--   2. If $y\in(-1,1)$ and $s^2W(y)\le1$, then $y+s\in(-1,1)$, $y-s\in(-1,1)$, and
--   $$u(y+s)+u(y-s)-2u(y)\le s^2W(y).\qquad(16)$$
--
--   The weight $W(y)$ is the per-coordinate cost in the curvature $D_v$; (16) bounds the curvature by $\sum_iv_i^2W(Y_i)/L^2$ and (15) controls its tail.
--
--   **Formalization Note** One $M_\eta$ serves both properties. $\log^{2+\eta}(ex)$ is $(\log(ex))^{2+\eta}$; the probability bound is compared as an extended nonnegative real.
--
--   Differences from the source:
--   - encoding: Y ∼ ρ with ρ(y) = Z⁻¹e^{−u(y)} on (−1, 1), u = +∞ off it → the law rho1 η (density by an indicator), u real-valued and read on (−1, 1) only; reason: u is never read off (−1, 1): the law vanishes there and (16) restricts y, y ± s
-- source:
--   Altschuler, Tikhomirov, Online Beck–Fiala Down to Logarithmic Sparsity, arXiv:2607.14238 (held version, sha256 5a1529d2…), p.8, Lemma 3.1, eqs. (14)–(16)

import Mathlib
import Definitions.Def_OnlineBeckFiala_W

open MeasureTheory

namespace OnlineBeckFiala

/-- **Lemma 3.1 (Curvature of u), p.8.** Altschuler, Tikhomirov, *Online Beck–Fiala Down to
Logarithmic Sparsity*, arXiv:2607.14238 (held version, sha256 5a1529d2…): "Let Y ∼ ρ. There are
constants M_η ≥ 1 and c_η, C_η > 0, each depending only on η, such that W(y) := M_η u(y) A(y)^{2+η}
(14) has the following properties. First, for every x ≥ 1,
P{W(Y) > x} ≤ C_η exp(−c_η x / log^{2+η}(ex)). (15)
Second, if y ∈ (−1, 1) and s²W(y) ≤ 1, then y ± s ∈ (−1, 1) and
u(y + s) + u(y − s) − 2u(y) ≤ s²W(y). (16)"

**Formalization Note.** `ρ` is the law `rho1 η` of §3.2 (`L = 1`). One `M` serves both (15) and
(16). `log^{2+η}(ex)` is `(log (e·x))^(2+η)` (real power; the base is `≥ 1`). The probability
bound is compared through `ENNReal.ofReal`. -/
theorem lemma_3_1 (η : ℝ) (hη : 0 < η) :
    ∃ M : ℝ, 1 ≤ M ∧ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ x : ℝ, 1 ≤ x →
        rho1 η {y | x < W η M y} ≤
          ENNReal.ofReal (C * Real.exp (-(c * x) / (Real.log (Real.exp 1 * x)) ^ (2 + η)))) ∧
      (∀ y ∈ Set.Ioo (-1 : ℝ) 1, ∀ s : ℝ, s ^ 2 * W η M y ≤ 1 →
        y + s ∈ Set.Ioo (-1 : ℝ) 1 ∧ y - s ∈ Set.Ioo (-1 : ℝ) 1 ∧
        u η (y + s) + u η (y - s) - 2 * u η y ≤ s ^ 2 * W η M y) := by sorry

end OnlineBeckFiala
