-- Prove2me | Theorems.Thm_GradSuffice_theorem_8
-- name    : GradSuffice.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:22:07.239014+00:00
-- url     : https://prove2.me/theorems/25ce9228-99ab-41be-a231-d9d44c76f60b
-- title:
--   Theorem 8, p.18 — a tree shattered by $W$ forces failure probability $\ge 7/8$ for $T\le D\kappa/4$ queries
-- statement:
--   Let $X$ be a real normed space with unit ball $B$, and let $W\subseteq B$ be convex and symmetric. Suppose that a $B^\star$-valued tree of depth $m$ is shattered by $W$ at margin $0<\theta<1$. Set $r:=\theta/256$ and $s:=r^2/8$, and for $0<\varepsilon\le s/4$ let
--   $$\kappa:=\Big\lfloor\frac{\log(1/(4\varepsilon))}{\log(1/s)}\Big\rfloor,\qquad D:=\Big\lfloor\Big(\frac{\theta^2m}{65536\log(16m^2)}\Big)^{1/3}\Big\rfloor ,$$
--   and assume $D\ge1$.
--
--   **Theorem 8.** There is a finitely supported distribution over convex, continuously differentiable, 1-Lipschitz functions $f$ such that every randomized first-order algorithm making at most $T\le D\kappa/4$ queries in $W$ and returning its last query $w_T$ satisfies
--   $$\Pr\Big\{f(w_T)-\inf_{w\in W}f(w)>\varepsilon\Big\}\ \ge\ \frac78,$$
--   the probability being over both the sampled function and the internal randomness of the algorithm.
--
--   Theorem 8 is the quantitative lower bound behind Theorem 4: it turns a deep shattered tree into an iteration-complexity lower bound of order $D\log(1/\varepsilon)$, for any convex symmetric domain, without duality.
--
--   Differences from the source:
--   - generalization: functions f : B → ℝ convex, continuously differentiable and 1-Lipschitz → functions X → ℝ convex, C¹ and 1-Lipschitz on all of X, answered by their gradient; reason: the construction lives on the ambient space (p.4); restricting to B gives the paper's functions, whose only subgradient is the gradient
--   - encoding: Pr over the sampled function and the internal randomness → ∑_f P(f) μ(failure set of f) for a finitely supported law P and a seed space (Ω, μ), the failure sets assumed measurable; reason: a probability is only defined for measurable sets
--   - encoding: at most T queries → exactly T ≥ 1 queries; reason: padding by repeating the last query; the output is the last query
--   - reading: log (no base printed) → natural logarithm Real.log; reason: the paper's constants (e.g. log m₀ / log(1/C), exp(cM)) are natural-log expressions
--   - reading: "a shattered tree … shattered by W at margin θ" with "let B⋆ be the dual of the unit ball" → the tree is B⋆-valued (IsDualValued ξ) and shattered by W at margin θ; reason: the theorem introduces B⋆ for the labels, p.11 states the bound "with subgradients in B⋆", and the proof uses ‖η_{t,k}‖⋆ ≤ 1 (p.20); without a bound on the labels any tree rescales to any margin
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), Theorem 8, p.18

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_NondualOpt_FinLaw
import Definitions.Def_GradSuffice_IsDualValued
import Definitions.Def_GradSuffice_IsShattered
import Definitions.Def_GradSuffice_DetAlg_lastQuery
import Definitions.Def_GradSuffice_thm8S
import Definitions.Def_GradSuffice_thm8Kappa
import Definitions.Def_GradSuffice_thm8D

namespace GradSuffice

/-- **Theorem 8 (lower bound from a tree shattered by `W`).** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, Theorem 8, p.18: "Let `W ⊆ B` be a
convex, symmetric, subset of the unit ball of a normed linear space, and let `B⋆` be the dual of the
unit ball. Suppose that there exists a shattered tree of depth `m` that is shattered by `W` at margin
`0 < θ < 1`. Set `r := θ/256`, `s := r²/8`. For every `0 < ε ≤ s/4`, define
`κ := ⌊log(1/(4ε))/log(1/s)⌋` and `D := ⌊(θ²m/(65536 log(16m²)))^{1/3}⌋`. Assume that `D ≥ 1`. Then
there exists a finitely supported distribution over convex, continuously differentiable,
1-Lipschitz functions `f : B → ℝ` such that every randomized first-order algorithm making at most
`T ≤ Dκ/4` queries and returning its last queried point `w_T` satisfies
`Pr{f(w_T) − inf_{w∈W} f(w) > ε} ≥ 7/8`. The probability is over both the sampled function and the
internal randomness of the algorithm."

**Formalization Note.** The distribution is a finitely supported law `P` on functions `X → ℝ` that
are convex, `C¹` and 1-Lipschitz on the whole space; the oracle of such `f` is its gradient
`fderiv ℝ f`. The shattered tree is `B⋆`-valued (`IsDualValued`): the theorem introduces
`B⋆` for its labels and the proof uses `‖η_{t,k}‖⋆ ≤ 1`. The algorithm has seed space `(Ω, μ)`, queries in `W`, and `T ≥ 1` queries (padding
covers fewer). The probability over the sampled function and the seed is
`∑_f P(f) μ(failure set of f)`; the failure sets are assumed measurable. -/
theorem theorem_8 (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] (W : Set X) (hWB : W ⊆ Metric.closedBall (0 : X) 1)
    (hWconv : Convex ℝ W) (hWsymm : ∀ w ∈ W, -w ∈ W) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (m : ℕ) (ξ : NondualOpt.Tree (StrongDual ℝ X) m) (hξ : IsDualValued ξ)
    (hsh : IsShattered W θ ξ) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ thm8S θ / 4)
    (hD : 1 ≤ thm8D θ m) :
    ∃ P : NondualOpt.FinLaw {f : X → ℝ | ConvexOn ℝ Set.univ f ∧ ContDiff ℝ 1 f ∧ LipschitzWith 1 f},
      ∀ T : ℕ, 0 < T → (T : ℝ) ≤ (thm8D θ m : ℝ) * (thm8Kappa θ ε : ℝ) / 4 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure μ] (A : Ω → DetAlg X W T),
        (∀ f ∈ P.w.support,
          MeasurableSet {ω | ε < f ((A ω).lastQuery f (fderiv ℝ f)) - sInf (f '' W)}) →
        (7 / 8 : ℝ) ≤ ∑ f ∈ P.w.support,
          P.w f * μ.real {ω | ε < f ((A ω).lastQuery f (fderiv ℝ f)) - sInf (f '' W)} := by sorry

end GradSuffice
