-- Prove2me | Theorems.Thm_HighDimStat_UniformLaws_symmetrization_sandwich
-- name    : HighDimStat.UniformLaws.symmetrization_sandwich
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:30:03.553296+00:00
-- url     : https://prove2.me/theorems/037fd7d4-c69e-4d05-98dd-ff1c7f0be673
-- title:
--   Proposition 4.11 -- the symmetrization sandwich
-- statement:
--   **Proposition 4.11 (symmetrization sandwich).** For any convex non-decreasing function
--   $\Phi:\mathbb R\to\mathbb R$,
--
--   $$
--   \mathbb E_{X,\varepsilon}\big[\Phi(\tfrac12\|S_n\|_{\bar F})\big] \;\le\;
--   \mathbb E_X\big[\Phi(\|\mathbb P_n-P\|_F)\big] \;\le\;
--   \mathbb E_{X,\varepsilon}\big[\Phi(2\|S_n\|_F)\big],
--   $$
--
--   where $\bar F=\{f-\mathbb E[f], f\in F\}$ is the recentered function class.
--
--   This "sandwich" result is what makes the symmetrization technique used in Theorem 4.10's
--   proof more than a one-off trick: it shows the empirical process $\|\mathbb P_n-P\|_F$ and
--   its symmetrized version $\|S_n\|_F$ are equivalent up to universal constants, for *any*
--   convex non-decreasing test function $\Phi$, not merely the identity used to prove Theorem
--   4.10 itself.
--
--   **Formalization Note** The lower bound uses the symmetrized process of the *recentered*
--   class $\bar F$ (realized as `fun j x => f j x - ∫ f j (X0)`), while the upper bound uses the
--   symmetrized process of the *original*, unrecentered class $F$ — kept asymmetric exactly as
--   the book's own displayed inequality (4.20), not "fixed" to use $\bar F$ on both sides.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 107 (PDF p. 127), Proposition 4.11, Eq. (4.20)

import Mathlib
import Definitions.Def_HighDimStat_UniformLaws_empProcessDeviation
import Definitions.Def_HighDimStat_UniformLaws_symmetrizedProcess

open MeasureTheory

namespace HighDimStat.UniformLaws

/-- **Proposition 4.11** (symmetrization sandwich), Wainwright, *High-Dimensional Statistics*
(2019), p. 107. For any convex non-decreasing `Φ : ℝ → ℝ`,
`E[Φ((1/2)‖Sₙ‖_F̄)] ≤ E[Φ(‖Pₙ-P‖_F)] ≤ E[Φ(2‖Sₙ‖_F)]`, where `F̄ = {f-E[f], f∈F}` is the
recentered function class. A hypothesis `hf` that each `f j` is measurable guards the Bochner
integrals against Mathlib's junk value on a non-integrable/non-measurable function. -/
theorem symmetrization_sandwich {D ι Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob] (f : ι → D → ℝ) (hf : ∀ j, Measurable (f j))
    (Xs : ℕ → Ω → D) (X0 : Ω → D) (eps : ℕ → Ω → ℝ)
    (n : ℕ) (Φ : ℝ → ℝ) (hΦconv : ConvexOn ℝ Set.univ Φ) (hΦmono : Monotone Φ)
    (hInt1 : Integrable (fun ω => Φ (1 / 2 *
      symmetrizedProcess (fun j x => f j x - ∫ ω', f j (X0 ω') ∂Prob) Xs eps n ω)) Prob)
    (hInt2 : Integrable (fun ω => Φ (empProcessDeviation f Xs X0 Prob n ω)) Prob)
    (hInt3 : Integrable (fun ω => Φ (2 * symmetrizedProcess f Xs eps n ω)) Prob) :
    ∫ ω, Φ (1 / 2 *
      symmetrizedProcess (fun j x => f j x - ∫ ω', f j (X0 ω') ∂Prob) Xs eps n ω) ∂Prob ≤
    ∫ ω, Φ (empProcessDeviation f Xs X0 Prob n ω) ∂Prob
    ∧
    ∫ ω, Φ (empProcessDeviation f Xs X0 Prob n ω) ∂Prob ≤
    ∫ ω, Φ (2 * symmetrizedProcess f Xs eps n ω) ∂Prob := by sorry

end HighDimStat.UniformLaws
