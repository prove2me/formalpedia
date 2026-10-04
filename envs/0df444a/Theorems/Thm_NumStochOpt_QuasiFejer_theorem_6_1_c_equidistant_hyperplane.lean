-- Prove2me | Theorems.Thm_NumStochOpt_QuasiFejer_theorem_6_1_c_equidistant_hyperplane
-- name    : NumStochOpt.QuasiFejer.theorem_6_1_c_equidistant_hyperplane
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T20:32:55.647442+00:00
-- url     : https://prove2.me/theorems/2e52fc2c-fc00-411b-8a01-017ec7033ad9
-- title:
--   Theorem 6.1 (c) — Z lies in the hyperplane equidistant from two accumulation points outside Z
-- statement:
--   Let $z^0,z^1,\dots$ be a stochastic quasi-Féjer sequence (Eq. (6.14)) for a set $Z\subseteq\mathbb R^n$ on a probability space $(\Theta,\mathcal R,\mu)$. Then for almost every $\theta$ the following holds: if $z'(\theta)$ and $z''(\theta)$ are two distinct accumulation points of $z^s(\theta)$ which do not belong to $Z$, then $Z$ lies in the hyperplane equidistant from $z'(\theta)$ and $z''(\theta)$, that is,
--   $$
--   \|z-z'(\theta)\|=\|z-z''(\theta)\|\qquad\text{for every } z\in Z.
--   $$
--
--   The exceptional null set is one set for all pairs of accumulation points and all $z\in Z$. In applications $Z$ is the solution set of an optimization problem; if one accumulation point is shown to lie in $Z$, this assertion forces convergence of the whole sequence.
--
--   **Formalization Note** For $z'\ne z''$ the set $\{z:\|z-z'\|=\|z-z''\|\}$ is the hyperplane of the book. The quantifier order is: almost surely, for all pairs of accumulation points. The book cites the proof to [5, p. 98].
-- source:
--   Yu. Ermoliev, "Stochastic Quasigradient Methods", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 6, p. 144, Theorem 6.1 (c)

import Mathlib
import Definitions.Def_NumStochOpt_QuasiFejer_ProjectionMethod
import Definitions.Def_NumStochOpt_QuasiFejer_StochQuasiFejer

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace NumStochOpt.QuasiFejer

/-- **Theorem 6.1 (c)** (Ermoliev, Ch. 6 of Ermoliev & Wets (1988), p. 144, citing [5, p. 98]).
If `{z^s}` is a stochastic quasi-Féjer sequence for `Z`, then for almost every outcome `ω`:
whenever `a ≠ b` are two accumulation points of `z^s(ω)` that do not belong to `Z`, the set `Z`
lies in the hyperplane `{w : ‖w - a‖ = ‖w - b‖}` equidistant from `a` and `b`. -/
theorem theorem_6_1_c_equidistant_hyperplane {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (Z : Set (EuclideanSpace ℝ (Fin n)))
    (hz : IsStochQuasiFejer μ z Z) :
    ∀ᵐ ω ∂μ, ∀ a b : EuclideanSpace ℝ (Fin n),
      MapClusterPt a atTop (fun s => z s ω) → MapClusterPt b atTop (fun s => z s ω) →
      a ≠ b → a ∉ Z → b ∉ Z → ∀ w ∈ Z, ‖w - a‖ = ‖w - b‖ := by sorry

end NumStochOpt.QuasiFejer
