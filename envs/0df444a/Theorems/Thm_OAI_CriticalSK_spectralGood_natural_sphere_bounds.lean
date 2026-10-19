-- Prove2me | Theorems.Thm_OAI_CriticalSK_spectralGood_natural_sphere_bounds
-- name    : OAI.CriticalSK.spectralGood_natural_sphere_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T21:37:18.726598+00:00
-- url     : https://prove2.me/theorems/010cacb5-5aa9-48f2-bd7a-a2d34e29a5ea
-- title:
--   Small-ball and overlap bounds for the tilted sphere measure on the GOE rigidity event (OpenAI, critical SK slow mixing)
-- statement:
--   Let $h \ge 0$ and $L \ge 262144$ be reals with `edgeFixedCost h L < 1/100` (`hh`, `hL`, `hcost`). For all large $n$, write $N = n + 4$. Let $\lambda$ be a spectrum (`lam : Fin N → ℝ`) in the rigidity event `spectralGood (n+3) h (naturalEdgeScale (n+3) L)`. That event says each $\lambda_i$ lies within the explicit error `edgeError` of the corresponding eigenvalue of the deterministic Jacobi path operator, at the edge scale $L/\ell^2$ with $\ell$ = `edgeLength (n+3)`. Let $\nu_\lambda$ = `sphereTilted lam 1 (Real.sqrt N)` be the probability measure on the unit sphere with density proportional to $\exp\bigl(\tfrac12\sum_i \lambda_i y_i^2\bigr)$, where $y = \sqrt N\,u$. Then both of the following hold.
--
--   1. **Small ball.** For every $b \ge 0$, the $\nu_\lambda$-probability that the coordinate $y_2$ satisfies $|y_2| \le b N^{1/3}$ is at most $C_L\, b$, where $C_L = 4\sqrt L\, e^{6L\sqrt L}$ (`naturalSmallBallConstant L`).
--   2. **Overlap.** $\dfrac{1}{N^2}\sum_i \Bigl(\int y_i^2 \, d\nu_\lambda\Bigr)^2 \le$ `naturalOverlapRate (n+3) L`.
--
--   All the named functions come from the definitions bundle `OAIQWCSK000` of this split. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.CriticalSK.spectralGood_natural_sphere_bounds`, OpenAI's lemma of that name in `lean/OAI/MathematicalPhysics/CriticalSK/SmallBall.lean`.
-- source:
--   OpenAI, Critical slowing down in the Sherrington–Kirkpatrick model, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-slowing-down-in-the-Sherrington-Kirkpatrick-model-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/SmallBall.lean (declaration OAI.CriticalSK.spectralGood_natural_sphere_bounds)

import Mathlib
import Definitions.Def_OAIQWCSK000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal

open scoped BigOperators NNReal

open scoped BigOperators

open scoped BigOperators InnerProductSpace

open Module

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal BigOperators

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set Real

open Finset Real

open scoped BigOperators ENNReal Topology

open Set MeasureTheory

open scoped BigOperators ENNReal

open MeasureTheory

open Finset Real Filter

open scoped Topology

namespace CriticalSK

section

open Set MeasureTheory Filter

lemma spectralGood_natural_sphere_bounds {h L : ℝ} (hh : 0 ≤ h) (hL : 262144 ≤ L)
    (hcost : edgeFixedCost h L < 1/100) :
    ∀ᶠ n : ℕ in atTop, ∀ lam ∈ spectralGood (n+3) h (naturalEdgeScale (n+3) L),
      (∀ b : ℝ, 0 ≤ b → (sphereTilted lam 1 (Real.sqrt (n+4))).real
        {u : unitSphere (Fin (n+4)) | |(Real.sqrt (n+4) • u.val) 2| ≤ b*(n+4:ℝ)^(1/3:ℝ)} ≤
        naturalSmallBallConstant L*b) ∧
      ((∑ i, (∫ u : unitSphere (Fin (n+4)), ((Real.sqrt (n+4) • u.val) i)^2
        ∂sphereTilted lam 1 (Real.sqrt (n+4)))^2)/(n+4:ℝ)^2 ≤ naturalOverlapRate (n+3) L) := by
  sorry

end

open Set MeasureTheory Filter

end CriticalSK

end

end OAI
end
