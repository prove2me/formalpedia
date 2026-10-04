-- Prove2me | Theorems.Thm_NumStochOpt_Bounds_property_e_expected_recourse_finite_convex
-- name    : NumStochOpt.Bounds.property_e_expected_recourse_finite_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T19:05:12.46105+00:00
-- url     : https://prove2.me/theorems/55b68a53-2605-4e63-8b60-6a9eb6488314
-- title:
--   Property (e) — the expected recourse function is finite and convex
-- statement:
--   Let $W$ have complete recourse, let $(\Omega,P)$ be a probability space and let $\xi(\omega)=(q(\omega),h(\omega),T(\omega))$ be random data whose every component has a finite second moment. Assume that $q(\omega)$ is dual feasible for every $\omega$ (some $u$ with $W^Tu\le q(\omega)$). Then:
--
--   1. $Q(x,\xi(\omega))$ is finite for every $x$ and every $\omega$;
--   2. $\omega\mapsto Q(x,\xi(\omega))$ is integrable for every $x$;
--   3. the expected recourse function
--   $$
--   \mathcal Q(x)=\int_\Omega Q(x,\xi(\omega))\,P(d\omega)
--   $$
--   is convex on $\mathbb R^{n_1}$.
--
--   Together with properties (a)–(d) this makes the two-stage problem (2.11) a finite convex program over the first-stage feasible set.
--
--   **Formalization Note** The book writes $Q$ for both $Q(x,\xi)$ and $\mathcal Q(x)$; in Lean they are `recourseCost` and `expectedRecourse`. The book states convexity "in $K$"; under the standing complete-recourse assumption $K=K_1$, and the statement is made on all of $\mathbb R^{n_1}$. The book's hypothesis of finite second moments is kept as stated (componentwise), although first moments would suffice.
-- source:
--   P. Kall, A. Ruszczyński, K. Frauendorfer, "Approximation Techniques in Stochastic Programming", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 2, p. 40, property (e) (standing assumptions pp. 39-40)

import Mathlib
import Definitions.Def_NumStochOpt_Bounds_RecourseCost

open MeasureTheory Matrix

namespace NumStochOpt.Bounds

/-- Property (e), p. 40: with complete recourse, `q(ω)` dual feasible for every `ω`, and random
data `ξ(ω) = (q(ω), h(ω), T(ω))` with finite second moments, the recourse cost is finite, its
expectation exists, and the expected recourse function `Q(x) = ∫ Q(x, ξ(ω)) P(dω)` is convex. -/
theorem property_e_expected_recourse_finite_convex {Ω ι κ ν : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] [Fintype ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Matrix ι κ ℝ) (hW : CompleteRecourse W)
    (q : Ω → κ → ℝ) (h : Ω → ι → ℝ) (T : Ω → Matrix ι ν ℝ)
    (hq2 : ∀ k, MemLp (fun ω => q ω k) 2 P) (hh2 : ∀ i, MemLp (fun ω => h ω i) 2 P)
    (hT2 : ∀ i j, MemLp (fun ω => T ω i j) 2 P)
    (hdual : ∀ ω, DualFeasible W (q ω)) :
    (∀ (x : ν → ℝ) (ω : Ω), recourseCost W (q ω) (h ω) (T ω) x ≠ ⊤ ∧
        recourseCost W (q ω) (h ω) (T ω) x ≠ ⊥) ∧
      (∀ x : ν → ℝ, Integrable (fun ω => (recourseCost W (q ω) (h ω) (T ω) x).toReal) P) ∧
      ConvexOn ℝ Set.univ (expectedRecourse P W q h T) := by sorry

end NumStochOpt.Bounds
