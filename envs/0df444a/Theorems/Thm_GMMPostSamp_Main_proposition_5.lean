-- Prove2me | Theorems.Thm_GMMPostSamp_Main_proposition_5
-- name    : GMMPostSamp.Main.proposition_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:28:59.849682+00:00
-- url     : https://prove2.me/theorems/7ec43c69-67f5-4025-b2aa-f12c4a521be1
-- title:
--   Proposition 5 — a well-conditioned sampler on a Euclidean ball: TV ≤ ξ with O(κd log(κd/ξ) log(κ(1 + Lr²))) gradient queries
-- statement:
--   There are an admissible program and a universal $C>0$ such that for all $d\ge1$, $\xi\in(0,\frac12)$, $\bar x\in\mathbb R^d$, $r>0$, $0<\mu\le L$ and every $V$ twice differentiable on $X=\{x:\|x-\bar x\|_2\le r\}$ with $\mu I_d\preceq\nabla^2V(x)\preceq LI_d$ for all $x\in X$ ($\kappa=L/\mu$): the program, given $(d,\xi,r,\mu,L,\bar x)$ and an oracle returning $\nabla V$ at a queried point, halts on every run after at most $C\kappa d\log(\frac{\kappa d}\xi)\log(\kappa(1+Lr^2))+C$ queries and within $C\kappa d^2\log(\frac{\kappa d}\xi)\log(\kappa(1+Lr^2))+C$ steps, outputs $\hat x\in X$, and
--   $$\mathrm{TV}\big(\mathrm{Law}(\hat x),\pi\big)\le\xi,\qquad\pi\propto e^{-V}\ \text{on }X.$$
--   It implements the oracle $O_c$ through the curvature bounds of Lemma 7.
--
--   **Formalization Note.** A query is one execution of the machine's oracle instruction, whose oracle maps the first $d$ queried cells $y$ to the coordinates of $\nabla V(y)$, the gradient taken within $X$ (and $0$ off $X$, where the page's $V$ is undefined). Derivatives are taken within $X$, so only the values of $V$ on $X$ matter.
--
--   Differences from the source:
--   - encoding: V : X → R twice-differentiable → V : ℝ^d → ℝ with V and its derivative within X differentiable on X (DifferentiableOn, fderivWithin); Hessian bounds as µ‖u‖² ≤ D²V(x)[u, u] ≤ L‖u‖² for x ∈ X with the second derivative within X; the oracle returns the gradient within X; reason: Lean functions are total; only values of V on X enter the hypotheses, the oracle answers on X and π
--   - reading: an algorithm that uses O(·) queries to ∇V and O(·) time → an admissible program receiving (d, ξ, r, µ, L, x̄) with a ∇V oracle instruction (one query per call); every run within C·(…) + C queries and C·(…) + C steps, C universal; reason: §2.1's real RAM with query access to ∇V; the algorithm knows the problem constants
--   - encoding: π ∈ P(X), π ∝ exp(−V) → the normalization of exp(−V) · Lebesgue restricted to X; reason: density with respect to Lebesgue measure
-- source:
--   Kumar, Sarkar, Tian, Zhu, Posterior Sampling in Gaussian Mixture Models Beyond the Clusterability Threshold, STOC 2027 submission (manuscript sha256 ba5079cd…), p. 24, Proposition 5; proof pp. 55–59

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_PolyVoting_dirichletMeasure
import Definitions.Def_GMMPostSamp_Main_Toolkit
import Definitions.Def_GMMPostSamp_Main_Model
import Definitions.Def_GMMPostSamp_Main_Machine

open MeasureTheory ProbabilityTheory

namespace GMMPostSamp.Main

/-- Proposition 5 (p. 24): there is a program that, given `(d, ξ, r, µ, L, x̄)` and oracle
access to `∇V` on `X`, for every `V` twice differentiable on `X = {x : ‖x − x̄‖₂ ≤ r}`
(derivatives within `X`, so only the values of `V` on `X` matter) with
`µ I ⪯ ∇²V ⪯ L I` there (`κ = L/µ`), halts on every run within
`C κd² log(κd/ξ) log(κ(1 + Lr²)) + C` steps after at most `C κd log(κd/ξ) log(κ(1 + Lr²)) + C`
queries to `∇V`, and outputs `x̂ ∈ X` with `TV(Law(x̂), π) ≤ ξ` for `π ∝ exp(−V)` on `X`. -/
theorem proposition_5 : ∃ P : Machine.Program, Machine.Admissible P ∧ ∃ C : ℝ, 0 < C ∧
    ∀ d : ℕ, 1 ≤ d → ∀ (ξ r μ L : ℝ) (xbar : E d) (V : E d → ℝ),
      0 < ξ → ξ < 1 / 2 → 0 < r → 0 < μ → μ ≤ L →
      DifferentiableOn ℝ V (Metric.closedBall xbar r) →
      DifferentiableOn ℝ (fderivWithin ℝ V (Metric.closedBall xbar r))
        (Metric.closedBall xbar r) →
      (∀ y ∈ Metric.closedBall xbar r, ∀ u : E d,
        μ * ‖u‖ ^ 2 ≤ fderivWithin ℝ (fderivWithin ℝ V (Metric.closedBall xbar r))
            (Metric.closedBall xbar r) y u u ∧
          fderivWithin ℝ (fderivWithin ℝ V (Metric.closedBall xbar r))
            (Metric.closedBall xbar r) y u u ≤ L * ‖u‖ ^ 2) →
      let κ : ℝ := L / μ
      let xs : List ℝ := [(d : ℝ), ξ, r, μ, L] ++ Machine.pointCells xbar
      let O : Machine.Oracle := fun q =>
        Machine.pointCells ((InnerProductSpace.toDual ℝ (E d)).symm
          (fderivWithin ℝ V (Metric.closedBall xbar r) ((EuclideanSpace.equiv (Fin d) ℝ).symm
            fun l => q.getD l 0)))
      Machine.RunsWithin P O xs
          (C * κ * (d : ℝ) ^ 2 * Real.log (κ * d / ξ) * Real.log (κ * (1 + L * r ^ 2)) + C)
          (C * κ * d * Real.log (κ * d / ξ) * Real.log (κ * (1 + L * r ^ 2)) + C) ∧
      (∀ τ : Machine.Tape, Machine.TapeOK τ → ∀ s, Machine.finalState P O xs τ = some s →
          Machine.decodePoint d 0 s ∈ Metric.closedBall xbar r) ∧
      tv (Machine.tapeLaw.map fun τ =>
            ((Machine.finalState P O xs τ).map (Machine.decodePoint d 0)).getD 0)
        (normalize (((volume : Measure (E d)).restrict (Metric.closedBall xbar r)).withDensity
          fun y => ENNReal.ofReal (Real.exp (-V y)))) ≤ ξ := by sorry

end GMMPostSamp.Main
