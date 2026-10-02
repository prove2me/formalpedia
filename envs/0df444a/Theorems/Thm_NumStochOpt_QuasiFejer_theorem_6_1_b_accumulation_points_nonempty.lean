-- Prove2me | Theorems.Thm_NumStochOpt_QuasiFejer_theorem_6_1_b_accumulation_points_nonempty
-- name    : NumStochOpt.QuasiFejer.theorem_6_1_b_accumulation_points_nonempty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T20:30:04.232664+00:00
-- url     : https://prove2.me/theorems/5fb0c22e-9c45-42cb-b215-7857bb6d221a
-- title:
--   Theorem 6.1 (b) — a stochastic quasi-Féjer sequence for a nonempty set has accumulation points a.s.
-- statement:
--   Let $z^0,z^1,\dots$ be a stochastic quasi-Féjer sequence (Eq. (6.14)) for a **nonempty** set $Z\subseteq\mathbb R^n$ on a probability space $(\Theta,\mathcal R,\mu)$. Then for almost every $\theta$ the set of accumulation points of the sequence $z^s(\theta)$, $s=0,1,\dots$, is not empty.
--
--   Together with part (c), this is how Theorem 6.1 turns into convergence of an algorithm: once one accumulation point is shown to lie in $Z$, the whole sequence converges.
--
--   **Formalization Note** The book does not state $Z\ne\emptyset$, but the definition is vacuous for $Z=\emptyset$ (then any sequence is quasi-Féjer, including $z^s=s\,e_1$), so the hypothesis is required and added. An accumulation point is a cluster point of $s\mapsto z^s(\theta)$ along `atTop` (`MapClusterPt`). The book cites the proof to [5, p. 98].
-- source:
--   Yu. Ermoliev, "Stochastic Quasigradient Methods", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 6, p. 144, Theorem 6.1 (b)

import Mathlib
import Definitions.Def_NumStochOpt_QuasiFejer_ProjectionMethod
import Definitions.Def_NumStochOpt_QuasiFejer_StochQuasiFejer

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace NumStochOpt.QuasiFejer

/-- **Theorem 6.1 (b)** (Ermoliev, Ch. 6 of Ermoliev & Wets (1988), p. 144, citing [5, p. 98]).
If `{z^s}` is a stochastic quasi-Féjer sequence for a nonempty set `Z`, then for almost every
outcome `ω` the sequence `z^s(ω)` has at least one accumulation point. -/
theorem theorem_6_1_b_accumulation_points_nonempty {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (Z : Set (EuclideanSpace ℝ (Fin n)))
    (hZ : Z.Nonempty) (hz : IsStochQuasiFejer μ z Z) :
    ∀ᵐ ω ∂μ, ∃ a : EuclideanSpace ℝ (Fin n), MapClusterPt a atTop (fun s => z s ω) := by sorry

end NumStochOpt.QuasiFejer
