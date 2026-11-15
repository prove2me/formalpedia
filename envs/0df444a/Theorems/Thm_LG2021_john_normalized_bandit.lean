-- Prove2me | Theorems.Thm_LG2021_john_normalized_bandit
-- name    : LG2021.john_normalized_bandit
-- status  : Proved
-- author  : @sim2000dg
-- created : 2026-11-14T15:49:07.496185+00:00
-- url     : https://prove2.me/theorems/b03c7a73-ea8c-45e9-bd82-1781e198e27a
-- title:
--   John normalization of explicit stochastic convex-bandit regret
-- statement:
--   For each ambient dimension $d$, there is a constant $C_d\ge0$ such that every nonempty compact convex set $K\subseteq\mathbb R^d$ admits, for each horizon $n\ge2$, a measurable randomized bandit policy supported on $K$ with expected regret at most $C_d\sqrt n\log^2 n$ for every continuous convex loss $L:K\to[0,1]$ and every admissible adaptive observation kernel. The probability space and policy precede the unknown loss and observation kernel. The noise is conditionally centered and satisfies the exponential-square moment bound $\mathbb E[\exp((Y-L(x))^2)\mid\mathrm{history},x]\le2$ at every legal query.
--
--   This is the John-normalized consequence of the explicit universal dimension and diameter bound in Theorem 1 of Lattimore and György (COLT 2021). The proof uses the affine hull of $K$, applies the proved Löwner–Fritz John theorem in that dimension, specializes the explicit rate using the diameter bound of the normalized body, and transports the resulting policy and adaptive kernels through the affine coordinate map. Singleton bodies have zero regret. The theorem does not assert a computational complexity bound.
-- source:
--   John and affine-hull transfer of Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, COLT 2021, PMLR 134:2938–2964, Theorem 1. The proved library Löwner–Fritz John theorem is reused; see Aharon Ben-Tal and Arkadi Nemirovski, Lectures on Modern Convex Optimization, SIAM, 2001, Theorem 4.9.1, p. 259.

import Mathlib
import Definitions.Def_LG2021_CanonicalBandit
open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set

theorem LG2021.john_normalized_bandit :
    ∀ d : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      ∀ K : Set (EuclideanSpace ℝ (Fin d)), K.Nonempty → IsCompact K → Convex ℝ K →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
          ∃ A : QueryAlg (EuclideanSpace ℝ (Fin d)) Ω, A.IsOn K ∧
            ∀ L : EuclideanSpace ℝ (Fin d) → ℝ,
              ContinuousOn L K → ConvexOn ℝ K L → (∀ x ∈ K, L x ∈ Icc 0 1) →
              ∀ ν : ObsKernel (EuclideanSpace ℝ (Fin d)), ν.IsMeasurable →
                UnitNoiseCond K L ν →
                  expectedCumLoss A P ν
                    (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n ≤
                      ENNReal.ofReal (C * Real.sqrt n * Real.log n ^ 2) := by sorry
