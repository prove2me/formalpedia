-- Prove2me | Theorems.Thm_OnlineDiscUniv_proposition_4_5
-- name    : OnlineDiscUniv.proposition_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:12.870888+00:00
-- url     : https://prove2.me/theorems/904883fc-4c5a-4f49-b213-03e391291256
-- title:
--   Proposition 4.5 — the pre-split simple predictable control with budget $c_\beta<c_\alpha$ and $\|d_a(Y^\beta_T)\|_{L^s}<\varepsilon$
-- statement:
--   Fix $\alpha>0$, a finite $s\ge2$ and $a>R_\alpha$. There are constants $c_0<c_\alpha$ and $h_0>0$ such that for every rational $h\in(0,h_0)$, every
--   $$
--   \frac{c_0}{\sqrt{1-h}}<c_\beta<c_\alpha,\qquad(4.8)
--   $$
--   and every $\varepsilon>0$, there is a bounded simple predictable control $\beta$ on $[0,T]$, $T=1-h$, with a finite rational description and
--   $$
--   \operatorname*{ess\,sup}_{0<t<T}\|\beta_t\|_{L^2}<c_\beta,\qquad\|d_a(Y^\beta_T)\|_{L^s}<\varepsilon,\qquad(4.9)
--   $$
--   where $Y^\beta_t=B_t+\int_0^t\beta_r\,dr$ and $d_a(x)=(|x|-a)_+$.
--
--   This is the control the algorithm follows before the final correction block.
--
--   Differences from the source:
--   - generalization: a fixed standard Brownian motion B with its completed natural filtration → every process B with IsBrownianReal B P on every probability space, the values computed on that B; reason: the Brownian control values depend only on the law of B; the source's Brownian motion is one such process
--   - generalization: constants c₀ < c_α and h₀ > 0 → constants with 0 ≤ c₀ < c_α and h₀ > 0; reason: a stronger conclusion (c₀ is moreover nonnegative); it implies the source's
--   - encoding: ess sup_{0<t<T} ‖β_t‖_{L²} < c_β; a > R_α → ess sup_{0<t<T} E β_t² < (ofReal c_β)²; R_α < ofReal a in ℝ≥0∞; reason: c_β > c₀/√(1−h) ≥ 0, so squaring preserves the inequality; same instances
--   - reading: All displayed inequalities may be given fixed positive slack. → not a separate clause; reason: a remark on strictness of the displayed inequalities, which are already strict
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), Proposition 4.5, (4.7)–(4.9), p.14 (PDF p.15)

import Mathlib
import Definitions.Def_OnlineDiscUniv_Ralpha
import Definitions.Def_OnlineDiscUniv_SimplePredCtrl
import Definitions.Def_OnlineDiscUniv_distA

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open ABPOnline (ctrlTerminal secondMoment)

namespace OnlineDiscUniv

/-- **Proposition 4.5** (Jo–Lee, arXiv:2610.00103, artifact sha256 cb190f12…, printed p.14,
PDF p.15). Fix `α > 0`, a finite `s ≥ 2`, and `a > R_α`. There are constants `c_0 < c_α` and
`h_0 > 0` such that for every rational `h ∈ (0, h_0)`, every `c_0/√(1 − h) < c_β < c_α` (4.8), and
every `ε > 0`, there is a bounded simple predictable control `β` on `[0,T]`, `T = 1 − h`, with a
finite rational description and `ess sup_{0<t<T} ‖β_t‖_{L²} < c_β`, `‖d_a(Y^β_T)‖_{L^s} < ε` (4.9),
where `Y^β_t = B_t + ∫_0^t β_r dr`.

**Formalization Note** The constant `c_0` is moreover nonnegative (a drift budget). The norm
bound on `β` is `ess sup_{0<t<T} E β_t² < c_β²` in `ℝ≥0∞`. The paper's closing sentence ("All
displayed inequalities may be given fixed positive slack") is a remark on strictness, not a
further clause. -/
theorem proposition_4_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (α : ℝ) (hα : 0 < α) (s : ℝ) (hs : 2 ≤ s)
    (a : ℝ) (ha : Ralpha P B α < ENNReal.ofReal a) :
    ∃ c₀ h₀ : ℝ, 0 ≤ c₀ ∧ c₀ < cAlpha α ∧ 0 < h₀ ∧
      ∀ h : ℚ, 0 < h → (h : ℝ) < h₀ → ∀ cβ : ℝ, c₀ / Real.sqrt (1 - h) < cβ → cβ < cAlpha α →
        ∀ ε : ℝ, 0 < ε → ∃ β : SimplePredCtrl, β.IsValidOn (1 - h) ∧
          essSup (secondMoment P (β.proc B)) (volume.restrict (Set.Ioo (0 : ℝ) (1 - h))) <
            ENNReal.ofReal cβ ^ 2 ∧
          eLpNorm (fun ω => distA a (ctrlTerminal B (β.proc B) ((1 - h : ℚ) : ℝ) ω))
            (ENNReal.ofReal s) P < ENNReal.ofReal ε := by sorry

end OnlineDiscUniv
