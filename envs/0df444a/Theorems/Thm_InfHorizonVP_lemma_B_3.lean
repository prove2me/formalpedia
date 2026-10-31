-- Prove2me | Theorems.Thm_InfHorizonVP_lemma_B_3
-- name    : InfHorizonVP.lemma_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:50.873804+00:00
-- url     : https://prove2.me/theorems/b45785ee-a41a-41a8-b6be-5f84cf46e90c
-- title:
--   Lemma B.3 (Kōmura [42]) — weak* differentiability a.e. of locally absolutely continuous p : ℝ₊ → E*
-- statement:
--   Let $E$ be a separable real Banach space and $p:\mathbb R_+\to E^*$ locally absolutely continuous (absolutely continuous on every $[0,\tau]$ for the dual norm). Then $p$ has a weak$^*$ derivative $\dot p(t)$ at almost every $t\in\mathbb R_+$.
--
--   Without reflexivity of $E$, $p$ need not be strongly differentiable anywhere; the weak$^*$ derivative is what gives meaning to the adjoint equation (iii) of Theorem 4.1.
--
--   **Formalization Note** Absolute continuity on $[0,\tau]$ is Mathlib's `AbsolutelyContinuousOnInterval`, equivalent to the page's definition by disjoint subintervals.
--
--   Differences from the source:
--   - encoding: locally absolutely continuous (p.11: sums over 0 ≤ t1 < τ1 ≤ t2 < … ≤ τ) → ∀ τ > 0, AbsolutelyContinuousOnInterval p 0 τ; reason: Mathlib's definition by finite families of disjoint subintervals is the same condition
--   - encoding: functions on ℝ₊ = [0, ∞) → functions on ℝ with every condition restricted to [0, ∞) (derivatives and weak* derivatives at t > 0); reason: Lean convention; values at negative times are never used, same instances
--   - encoding: E* the norm dual; ẋ the strong derivative → E →L[ℝ] ℝ with the operator norm; deriv x; reason: Lean convention; same objects (deriv agrees with the strong derivative wherever it exists, which is a.e.)
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, Lemma B.3, p.30 (PDF p.31)

import Mathlib
import Definitions.Def_InfHorizonVP_HasWeakStarDerivAt
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Lemma B.3 (Kōmura [42]) — locally absolutely continuous dual-valued functions are weak\*
differentiable almost everywhere.**
Frankowska, Sagara, arXiv:1801.00400v3, Lemma B.3, p.30: "Let E be a separable Banach space. Then
every locally absolutely continuous function p : R+ → E* possesses the weak* derivative ṗ(t) a.e.
t ∈ R+." Local absolute continuity (p.11): "its restriction to the bounded closed interval [0, τ]
is absolutely continuous for every τ > 0, i.e., for every τ > 0 and ε > 0 there exists δ > 0 such
that 0 ≤ t1 < τ1 ≤ t2 < τ2 < · · · ≤ tn < τn ≤ τ and Σ|ti − τi| < δ imply Σ‖p(ti) − p(τi)‖ < ε."

**Formalization Note.** Absolute continuity on `[0, τ]` is Mathlib's
`AbsolutelyContinuousOnInterval p 0 τ` (finite families of disjoint subintervals, distance in the
dual norm of `E* = E →L[ℝ] ℝ`), equivalent to the page's definition. The weak\* derivative is
two-sided, at `t > 0` (p.11). -/
theorem lemma_B_3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (p : ℝ → E →L[ℝ] ℝ) (hp : ∀ τ, 0 < τ → AbsolutelyContinuousOnInterval p 0 τ) :
    ∀ᵐ t ∂(volume.restrict (Ioi 0)), ∃ y : E →L[ℝ] ℝ, HasWeakStarDerivAt p y t := by sorry

end InfHorizonVP
