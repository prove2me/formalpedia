-- Prove2me | Theorems.Thm_OnlineDiscUniv_proposition_2_1
-- name    : OnlineDiscUniv.proposition_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:14:57.435264+00:00
-- url     : https://prove2.me/theorems/097afecd-0107-4325-a573-002b37e84f48
-- title:
--   Proposition 2.1 — properties of the Brownian value: attainment, continuity and monotonicity of $R(c)$, monotonicity of $V^\infty_T$, finiteness of $\ell_\star$
-- statement:
--   Let $B$ be a standard Brownian motion and let $R(c)$, $V^\infty_T$ be the Brownian control values of (2.3)–(2.4). Then:
--
--   1. the infimum in (2.4) is attained: for every $c\ge0$ there is an admissible control $u$ with $\|B_1+\int_0^1u_t\,dt\|_{L^\infty}=R(c)$;
--   2. $c\mapsto R(c)$ is continuous and nonincreasing on $(0,\infty)$;
--   3. $T\mapsto V^\infty_T$ is nondecreasing;
--   4. $\ell_\star:=\lim_{T\to\infty}V^\infty_T$ exists and is finite.
--
--   These are the analytic facts about the Brownian value used to choose the control of the algorithm (Proposition 4.5) and to state the threshold asymptotics.
--
--   Differences from the source:
--   - generalization: a fixed standard Brownian motion B with its completed natural filtration → every process B with IsBrownianReal B P on every probability space, the values computed on that B; reason: the Brownian control values depend only on the law of B; the source's Brownian motion is one such process
--   - encoding: R(c), V^∞_T, ℓ⋆ real-valued (possibly infinite) → values in ℝ≥0∞, real bounds embedded by ENNReal.ofReal; reason: the same inequalities and limits; avoids junk values of sInf ∅ and toReal ⊤
--   - encoding: the infimum in (2.4) is attained; ℓ⋆ is finite; T ↦ V^∞_T nondecreasing → ∃ admissible u with eLpNorm (B_1 + ∫u) ∞ = R(c), for every c ≥ 0; the limit exists in ℝ≥0∞ and is < ⊤; MonotoneOn on T > 0; reason: (2.4) is posed for c ≥ 0 and (2.3) for T > 0; at c = 0 the value is ∞ (p.6), also attained
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), Proposition 2.1, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_OnlineDiscUniv_Ralpha

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open ABPOnline (ctrlTerminal)

namespace OnlineDiscUniv

/-- **Proposition 2.1** (Jo–Lee, *Exact Universality of Online Discrepancy*, arXiv:2610.00103,
artifact sha256 cb190f12…, printed p.6, PDF p.7). The infimum in (2.4) is attained. The map
`c ↦ R(c)` is continuous and nonincreasing on `(0, ∞)`, the map `T ↦ V^∞_T` is nondecreasing,
and `ℓ⋆ := lim_{T→∞} V^∞_T` is finite.

**Formalization Note** `B` is any standard Brownian motion on any probability space (the values
depend only on its law). Values are in `ℝ≥0∞`: attainment means an admissible control whose
terminal `L∞` radius equals `R(c)`, for every `c ≥ 0` (at `c = 0`, `R(0) = ∞`, p.6);
"`T ↦ V^∞_T` nondecreasing" is on `T > 0`, where `V^∞_T` is defined; "`ℓ⋆` finite" means the
limit exists in `ℝ≥0∞` and is `< ∞`. -/
theorem proposition_2_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    (∀ c : ℝ, 0 ≤ c → ∃ u : ℝ≥0 → Ω → ℝ, IsAdmCtrl P B 1 c u ∧
      eLpNorm (ctrlTerminal B u 1) ⊤ P = Rc P B c) ∧
    ContinuousOn (Rc P B) (Set.Ioi 0) ∧ AntitoneOn (Rc P B) (Set.Ioi 0) ∧
    MonotoneOn (Vinf P B) (Set.Ioi 0) ∧
    ∃ ℓ : ℝ≥0∞, Tendsto (Vinf P B) atTop (𝓝 ℓ) ∧ ℓ < ⊤ := by sorry

end OnlineDiscUniv
