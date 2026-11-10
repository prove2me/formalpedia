-- Prove2me | Theorems.Thm_OnlineDiscUniv_proposition_4_2
-- name    : OnlineDiscUniv.proposition_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:29.753261+00:00
-- url     : https://prove2.me/theorems/e48797cd-836d-4936-877c-2b7310419ef4
-- title:
--   Proposition 4.2 — $r_{c,T}=\sqrt T\,R(c\sqrt T)$ and bounded controls approaching it in $L^p$
-- statement:
--   Fix $c>0$, $1\le p<\infty$ and $T\in(0,1]$. The optimal terminal radius on horizon $T$ with pointwise $L^2$ drift bound $c$ is
--   $$
--   r_{c,T}:=\inf\Big\{\Big\|B_T+\int_0^Tu_t\,dt\Big\|_{L^\infty}\Big\}=\sqrt T\,R(c\sqrt T).\qquad(4.3)
--   $$
--   There are bounded controls $u^{(n)}$ on $[0,T]$, progressively measurable with respect to the natural Brownian filtration, with $\|u^{(n)}_t\|_{L^2}\le c$ for a.e. $t$, such that, with $Y^{(n)}_T=B_T+\int_0^Tu^{(n)}_t\,dt$,
--   $$
--   \big\|(|Y^{(n)}_T|-r_{c,T})_+\big\|_{L^p}\longrightarrow0.\qquad(4.4)
--   $$
--
--   This supplies the bounded Brownian control from which the algorithm's simple predictable control is built (Proposition 4.5).
--
--   Differences from the source:
--   - generalization: a fixed standard Brownian motion B with its completed natural filtration → every process B with IsBrownianReal B P on every probability space, the values computed on that B; reason: the Brownian control values depend only on the law of B; the source's Brownian motion is one such process
--   - reading: progressively measurable with respect to the natural Brownian filtration → progressively measurable for the completed natural filtration F^B; reason: §2.2 defines F^B as the completed natural filtration and Appendix A projects onto it; the paper uses the two names for the same filtration
--   - encoding: r_{c,T} and R(c√T) real-valued (possibly infinite) → values in ℝ≥0∞, real bounds embedded by ENNReal.ofReal; reason: the same inequalities and limits; avoids junk values of sInf ∅ and toReal ⊤
--   - encoding: the radius r_{c,T} in (4.4); bounded controls → the real number (√T · R(c√T)).toReal; a uniform bound |u_t(ω)| ≤ K for t ≤ T; reason: R(c√T) is finite for c√T > 0 (Proposition 2.1), so toReal returns the value
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), Proposition 4.2, (4.3)–(4.4), p.13 (PDF p.14)

import Mathlib
import Definitions.Def_OnlineDiscUniv_Ralpha

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open ABPOnline (ctrlTerminal)

namespace OnlineDiscUniv

/-- **Proposition 4.2** (Jo–Lee, arXiv:2610.00103, artifact sha256 cb190f12…, printed p.13,
PDF p.14). Fix `c > 0`, `1 ≤ p < ∞`, and `T ∈ (0, 1]`. The optimal terminal radius on horizon
`T` with pointwise `L²` drift bound `c` is `r_{c,T} := √T R(c√T)` (4.3). There are bounded controls
`u^{(n)}` on `[0,T]`, progressively measurable with respect to the natural Brownian filtration,
with `‖u^{(n)}_t‖_{L²} ≤ c` for a.e. `t`, such that `‖(|Y^{(n)}_T| − r_{c,T})_+‖_{L^p} → 0` (4.4),
where `Y^{(n)}_T = B_T + ∫_0^T u^{(n)}_t dt`.

**Formalization Note** The first clause states (4.3) as the identity
`ctrlVal P B T c = √T · R(c√T)` in `ℝ≥0∞`. In (4.4) the radius is the real number
`(√T · R(c√T)).toReal`; `R(c√T)` is finite for `c√T > 0` (Proposition 2.1). "Bounded" means a
uniform bound on `[0,T] × Ω`. The natural Brownian filtration is the completed one, as in §2.2
and Appendix A. -/
theorem proposition_4_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (c p T : ℝ) (hc : 0 < c) (hp : 1 ≤ p)
    (hT0 : 0 < T) (hT1 : T ≤ 1) :
    ctrlVal P B T c = ENNReal.ofReal (Real.sqrt T) * Rc P B (c * Real.sqrt T) ∧
    ∃ u : ℕ → ℝ≥0 → Ω → ℝ,
      (∀ n, IsAdmCtrl P B T c (u n) ∧ ∃ K : ℝ, ∀ (t : ℝ≥0) (ω : Ω), (t : ℝ) ≤ T → |u n t ω| ≤ K) ∧
      Tendsto (fun n => eLpNorm (fun ω => max (|ctrlTerminal B (u n) T ω| -
          (ENNReal.ofReal (Real.sqrt T) * Rc P B (c * Real.sqrt T)).toReal) 0)
          (ENNReal.ofReal p) P) atTop (𝓝 0) := by sorry

end OnlineDiscUniv
