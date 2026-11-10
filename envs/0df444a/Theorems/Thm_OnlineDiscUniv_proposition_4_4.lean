-- Prove2me | Theorems.Thm_OnlineDiscUniv_proposition_4_4
-- name    : OnlineDiscUniv.proposition_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:13:07.13465+00:00
-- url     : https://prove2.me/theorems/79441d06-e4d6-45fd-965b-aa9a295f03ce
-- title:
--   Proposition 4.4 — approximation by simple predictable controls with a finite rational description
-- statement:
--   Let $T>0$ be rational and let $u$ be a bounded control on $[0,T]$, progressively measurable with respect to the natural Brownian filtration, with
--   $$
--   \operatorname*{ess\,sup}_{0<t<T}\|u_t\|_{L^2}\le c_0 .
--   $$
--   Fix $c_1>c_0$, $1\le p<\infty$ and $\varepsilon>0$. There is a bounded simple predictable control $\beta$ of the form (4.5), with a finite rational description, such that
--   $$
--   \operatorname*{ess\,sup}_{0<t<T}\|\beta_t\|_{L^2}<c_1,\qquad\Big\|\int_0^T(\beta_t-u_t)\,dt\Big\|_{L^p}<\varepsilon.\qquad(4.6)
--   $$
--
--   Simple predictable controls are what the online algorithm can evaluate; this proposition shows that nothing is lost in the drift budget or the terminal value by restricting to them.
--
--   Differences from the source:
--   - generalization: a fixed standard Brownian motion B with its completed natural filtration → every process B with IsBrownianReal B P on every probability space, the values computed on that B; reason: the Brownian control values depend only on the law of B; the source's Brownian motion is one such process
--   - reading: progressively measurable with respect to the natural Brownian filtration → progressively measurable for the completed natural filtration F^B; reason: §2.2 defines F^B as the completed natural filtration and Appendix A projects onto it; the paper uses the two names for the same filtration
--   - encoding: ess sup_{0<t<T} ‖u_t‖_{L²} ≤ c₀ (and < c₁ for β) → ess sup_{0<t<T} E u_t² ≤ (ofReal c₀)² in ℝ≥0∞ with 0 ≤ c₀ (and < (ofReal c₁)² for β); reason: squaring is monotone on norms; c₀ < 0 only gives an unsatisfiable hypothesis in the source
--   - encoding: all times rational; β_t on (t_j, t_{j+1}] → SimplePredCtrl stores rational times; β_0 := 0; reason: a finite rational description requires rational times; a single time is Lebesgue-null
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), Proposition 4.4, (4.6), p.14 (PDF p.15); Definition 4.3, pp.13–14 (PDF pp.14–15)

import Mathlib
import Definitions.Def_ABPOnline_Estar
import Definitions.Def_OnlineDiscUniv_IsProgOn
import Definitions.Def_OnlineDiscUniv_SimplePredCtrl

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open ABPOnline (brownFiltration secondMoment)

namespace OnlineDiscUniv

/-- **Proposition 4.4** (Jo–Lee, arXiv:2610.00103, artifact sha256 cb190f12…, printed p.14,
PDF p.15). Let `T > 0` be rational and let `u` be a bounded control on `[0,T]`, progressively
measurable with respect to the natural Brownian filtration, with `ess sup_{0<t<T} ‖u_t‖_{L²} ≤ c_0`.
Fix `c_1 > c_0`, `1 ≤ p < ∞`, and `ε > 0`. There is a bounded simple predictable control `β` of
the form (4.5), with a finite rational description, such that `ess sup_{0<t<T} ‖β_t‖_{L²} < c_1`
and `‖∫_0^T (β_t − u_t) dt‖_{L^p} < ε` (4.6).

**Formalization Note** `ess sup_{0<t<T} ‖u_t‖_{L²} ≤ c_0` is written as
`ess sup_{0<t<T} E u_t² ≤ c_0²` in `ℝ≥0∞`, and likewise for `β` with strict inequality; the
hypothesis `0 ≤ c_0` only excludes values for which the paper's hypothesis (a norm bounded by a
negative number) is unsatisfiable. The natural Brownian filtration is the completed one (§2.2). -/
theorem proposition_4_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (T : ℚ) (hT : 0 < T) (u : ℝ≥0 → Ω → ℝ)
    (hu : IsProgOn (brownFiltration P B) T u)
    (hbdd : ∃ K : ℝ, ∀ (t : ℝ≥0) (ω : Ω), (t : ℝ) ≤ (T : ℝ) → |u t ω| ≤ K) (c₀ : ℝ) (hc₀ : 0 ≤ c₀)
    (hbudget : essSup (secondMoment P u) (volume.restrict (Set.Ioo (0 : ℝ) T)) ≤
      ENNReal.ofReal c₀ ^ 2)
    (c₁ p ε : ℝ) (hc₁ : c₀ < c₁) (hp : 1 ≤ p) (hε : 0 < ε) :
    ∃ β : SimplePredCtrl, β.IsValidOn T ∧
      essSup (secondMoment P (β.proc B)) (volume.restrict (Set.Ioo (0 : ℝ) T)) <
        ENNReal.ofReal c₁ ^ 2 ∧
      eLpNorm (fun ω => ∫ t in Set.Icc (0 : ℝ) T, (β.proc B t.toNNReal ω - u t.toNNReal ω))
        (ENNReal.ofReal p) P < ENNReal.ofReal ε := by sorry

end OnlineDiscUniv
