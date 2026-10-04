-- Prove2me | Theorems.Thm_NumStochOpt_QuasiFejer_theorem_6_1_a_norm_converges
-- name    : NumStochOpt.QuasiFejer.theorem_6_1_a_norm_converges
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T20:27:55.350065+00:00
-- url     : https://prove2.me/theorems/7b05b9da-2e8f-4a0d-a30c-d166e00bf748
-- title:
--   Theorem 6.1 (a) — distances to Z of a stochastic quasi-Féjer sequence converge a.s. and have bounded mean square
-- statement:
--   Let $z^0,z^1,\dots$ be a stochastic quasi-Féjer sequence for a set $Z\subseteq\mathbb R^n$ on a probability space $(\Theta,\mathcal R,\mu)$ (Eq. (6.14)). Then for every $z\in Z$:
--
--   1. the sequence $\|z-z^{s+1}\|^2$, $s=0,1,\dots$, converges with probability 1;
--   2. there is a constant $C<\infty$ with
--   $$
--   E\|z-z^s\|^2<C\qquad\text{for all } s.
--   $$
--
--   The exceptional null set in (1) and the constant $C$ in (2) may depend on $z$. This is the basic stability property of quasi-Féjer sequences; parts (b) and (c) of Theorem 6.1 and the convergence proof of the projection method (Theorem 6.2) rest on it.
--
--   **Formalization Note** $E\|z-z^s\|^2$ is a lower Lebesgue integral in $[0,\infty]$ and $C$ is an element of $[0,\infty)$. The book cites the proof to [5, p. 98] (Ermoliev 1976).
-- source:
--   Yu. Ermoliev, "Stochastic Quasigradient Methods", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 6, p. 144, Theorem 6.1 (a)

import Mathlib
import Definitions.Def_NumStochOpt_QuasiFejer_ProjectionMethod
import Definitions.Def_NumStochOpt_QuasiFejer_StochQuasiFejer

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace NumStochOpt.QuasiFejer

/-- **Theorem 6.1 (a)** (Ermoliev, Ch. 6 of Ermoliev & Wets (1988), p. 144, citing [5, p. 98]).
If `{z^s}` is a stochastic quasi-Féjer sequence for `Z`, then for every `w ∈ Z` the sequence
`‖w - z^{s+1}‖²` converges with probability 1 (the null set may depend on `w`), and
`E‖w - z^s‖²` is bounded in `s` by a finite constant `C` (which may depend on `w`). -/
theorem theorem_6_1_a_norm_converges {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (Z : Set (EuclideanSpace ℝ (Fin n)))
    (hz : IsStochQuasiFejer μ z Z) :
    ∀ w ∈ Z,
      (∀ᵐ ω ∂μ, ∃ l : ℝ, Tendsto (fun s => ‖w - z (s + 1) ω‖ ^ 2) atTop (𝓝 l)) ∧
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ s, ∫⁻ ω, ENNReal.ofReal (‖w - z s ω‖ ^ 2) ∂μ < C := by sorry

end NumStochOpt.QuasiFejer
