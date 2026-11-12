-- Prove2me | Theorems.Thm_FreeProbAMP_StateEvolution_finite_history_ranks
-- name    : FreeProbAMP.StateEvolution.finite_history_ranks
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:27:23.089705+00:00
-- url     : https://prove2.me/theorems/1b0c48c0-09be-4fba-b2a1-54d2070f89d1
-- title:
--   Proposition 5.2 — finite-sample history ranks
-- statement:
--   Let $A$ be the normalized independent GOE input, $u^0$ an independent random initialization, and let the deterministic coefficients and nonlinearities satisfy Assumptions 2.3 and 2.5 through horizon $T$. All inputs are random variables in the standing measurable sense, in particular $g_0$ is measurable. If $n\ge T+1$ and $d(d+1)/2\ge T+1$, then almost surely, simultaneously for $0\le t\le T$,
--
--   $$\operatorname{rank}[m^0|\cdots|m^t]=\operatorname{rank}[M^0|\cdots|M^t]=t+1.$$
--
--   The messages are those of the actual AMP recursion, with the zero negative-time boundary. This is a finite-size rank conclusion used to justify history Gram inverses. No global growth, smoothness, or asymptotic convergence hypothesis is needed for this finite-size assertion.
--
--   Differences from the source:
--   - generalization: initialization satisfying the common-array all-moment convergence of Assumption 2.2 → any independent measurable initialization at the fixed finite size; reason: the finite-size rank conclusion uses only independence; every source initialization specializes to such a vector
--   - encoding: the t+1 columns have rank t+1 → the t+1 columns are linearly independent over the reals; reason: equivalent full-column-rank statement
--   - encoding: random vectors and matrix observations → explicit measurability of random data and almost-everywhere symmetry; reason: the standing random-variable convention is made explicit; no distribution is excluded
-- source:
--   August Chen, Ahmed El Alaoui, STOC 2027 submission #1182 (October 2026), p. 28, Proposition 5.2, (5.2); Assumptions 2.2, 2.3, 2.5

import Mathlib
import Definitions.Def_FreeProbAMP_StateEvolution_History

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal Matrix
set_option autoImplicit false
noncomputable section

namespace FreeProbAMP.StateEvolution

/-- Proposition 5.2, submission p.28. Independence of t+1 columns is rank t+1.
Measurability of g_0 is the standing random-variable convention; no C1 assumption is made. -/
theorem finite_history_ranks
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n d T : ℕ) (hn : 0 < n) (hd : 0 < d)
    (A : Ω → Fin n → RMat d) (u₀ : Ω → Fin n → ℝ)
    (a : ℕ → ℕ → ℝ) (g : ScalarMaps)
    (hgoe : GOEArray μ A) (hu : Measurable u₀) (hi : IndepFun u₀ A μ)
    (ha : Coefficients T a) (hg : LastLinear T g) (hm : Measurable (g 0))
    (hnd : T+1 ≤ n) (hdd : T+1 ≤ d*(d+1)/2) :
    ∀ᵐ ω ∂μ, ∀ t, t ≤ T →
      LinearIndependent ℝ (fun s : Fin (t+1) => mIter (A ω) a g (u₀ ω) s) ∧
      LinearIndependent ℝ (fun s : Fin (t+1) => matIter (A ω) a g (u₀ ω) s) := by sorry

end FreeProbAMP.StateEvolution
