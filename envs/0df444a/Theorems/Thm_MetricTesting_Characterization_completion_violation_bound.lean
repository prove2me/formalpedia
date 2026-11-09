-- Prove2me | Theorems.Thm_MetricTesting_Characterization_completion_violation_bound
-- name    : MetricTesting.Characterization.completion_violation_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:33.835393+00:00
-- url     : https://prove2.me/theorems/443203ba-55ee-43c7-ae32-5eaa37d6c416
-- title:
--   Lemma 3.8 — Holes bound violation density
-- statement:
--   Fix the standing local matrix framework with nonempty valid targets. Let $A$ be a locally consistent partial array on $n\ge k$ vertices, and let $D$ be any completion which preserves all specified entries. For a real parameter $\theta$, if $|H(A)|\le\theta n^2$, then
--   $$\operatorname{viol}(D)\le4\binom k2\theta.$$
--   The completion need not be valid. The hole bound already forces $\theta\ge0$ because $n\ge k\ge2$. This estimate transfers sparse missing data to a bound on violations, while retaining the source's exact coefficient.
--
--   Differences from the source:
--   - encoding: matrices on [n] with off-diagonal values in Λ and zero diagonal → functions from two-element subsets of Fin n to the subtype Λ of nonnegative reals; reason: this is a bijective encoding of all source matrices; relabelling uses injections and no metric axiom is imposed
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), p. 11, Lemma 3.8 (PDF p. 12)

import Definitions.Def_MetricTesting_Characterization_moduli

set_option autoImplicit false

noncomputable section

namespace MetricTesting.Characterization

/-- Lemma 3.8, printed p.11 / PDF p.12. D need not be valid. -/
theorem completion_violation_bound (F : LocalData) (hP : TargetsNonempty F)
    (n : ℕ) (hn : F.k ≤ n) (A : PartialArray F.values n)
    (hA : LocallyConsistent F A) (D : Array F.values n) (hD : Completes A D)
    (θ : ℝ) (hH : (Holes A).card ≤ θ * (n : ℝ)^2) :
    violationDensity F D ≤ 4 * (Nat.choose F.k 2 : ℝ) * θ := by sorry

end MetricTesting.Characterization
