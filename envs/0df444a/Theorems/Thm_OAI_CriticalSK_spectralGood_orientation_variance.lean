-- Prove2me | Theorems.Thm_OAI_CriticalSK_spectralGood_orientation_variance
-- name    : OAI.CriticalSK.spectralGood_orientation_variance
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T21:37:20.36641+00:00
-- url     : https://prove2.me/theorems/8764bf5f-3a29-429b-a2a9-bfa3cfef9514
-- title:
--   Haar variance of the rotated-cube partition function on the GOE rigidity event (OpenAI, critical SK slow mixing)
-- statement:
--   Let $h \ge 0$ and $L \ge 262144$ be reals with `edgeFixedCost h L < 1/100` (`hh`, `hL`, `hcost`), and let $\varepsilon > 0$ (`hε`). For all large $n$, write $N = n + 4$. Let $\lambda$ be a spectrum (`lam : Fin N → ℝ`) in the rigidity event `spectralGood (n+3) h (naturalEdgeScale (n+3) L)`. Then
--   $$\int \Bigl(\frac{Z_{\mathrm{cube}}(U)}{Z_{\mathrm{sph}}(\lambda)} - 1\Bigr)^2 \, dU \;\le\; \varepsilon + \texttt{naturalOrientationTail}\ (n+3)\ L .$$
--   The quantities are:
--   - $Z_{\mathrm{cube}}(U)$ = `rotatedCubePartition lam 1 U` is the average of $\exp\bigl(\tfrac12\sum_i\lambda_i (Ux)_i^2\bigr)$ over $x \in \{\pm1\}^N$;
--   - $Z_{\mathrm{sph}}(\lambda)$ = `spherePartition lam 1 (Real.sqrt N)` is the average of $\exp\bigl(\tfrac12\sum_i\lambda_i y_i^2\bigr)$ over the sphere of radius $\sqrt N$;
--   - $dU$ is the Haar probability measure on the orthogonal group (`orthogonalHaar (Fin N)`).
--
--   All the named functions come from the definitions bundle `OAIQWCSK000` of this split. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.CriticalSK.spectralGood_orientation_variance`, OpenAI's lemma of that name in `lean/OAI/MathematicalPhysics/CriticalSK/OrientationLimits.lean`.
-- source:
--   OpenAI, Critical slowing down in the Sherrington–Kirkpatrick model, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-slowing-down-in-the-Sherrington-Kirkpatrick-model-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/OrientationLimits.lean (declaration OAI.CriticalSK.spectralGood_orientation_variance)

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

open Set MeasureTheory Filter

lemma spectralGood_orientation_variance {h L : ℝ} (hh : 0 ≤ h) (hL : 262144 ≤ L)
    (hcost : edgeFixedCost h L < 1/100) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ lam ∈ spectralGood (n+3) h (naturalEdgeScale (n+3) L),
      (∫ U, (rotatedCubePartition lam 1 U/spherePartition lam 1 (Real.sqrt (n+4))-1)^2
        ∂orthogonalHaar (Fin (n+4))) ≤ ε+naturalOrientationTail (n+3) L := by
  sorry

end CriticalSK

end

end OAI
end
