-- Prove2me | Theorems.Thm_OAI_CriticalSK_orientation_normalized_variance_bound
-- name    : OAI.CriticalSK.orientation_normalized_variance_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T21:37:12.871877+00:00
-- url     : https://prove2.me/theorems/38bf15cb-c742-4ef7-9eda-b767f22be716
-- title:
--   Normalized Haar variance of the rotated-cube partition function under explicit spectral hypotheses (OpenAI, critical SK slow mixing)
-- statement:
--   Let $\varepsilon > 0$ (`hε`). For all large $n$ the following holds. Let $\lambda \in \mathbb{R}^n$ be a spectrum (`lam : Fin n → ℝ`). Let $u, v \in \mathbb{R}^n$ be orthogonal vectors of norm $\sqrt n$, and let $K > 0$ and $s_0 \ge 0$ be reals. Assume:
--
--   1. $|\lambda_i| \le 3$ for all $i$;
--   2. $K e^{n\,\Phi(\lambda)} \le Z_{\mathrm{sph}}(\lambda)$. Here $Z_{\mathrm{sph}}(\lambda)$ = `spherePartition lam 1 (Real.sqrt n)` is the average of $\exp\bigl(\tfrac12\sum_i \lambda_i y_i^2\bigr)$ over the sphere of radius $\sqrt n$. And $\Phi(\lambda)$ = `sphericalVariational lam 1` is the infimum, over $z > \max_i \lambda_i$, of $\tfrac{z-1}{2} - \tfrac1{2n}\sum_i \log(z - \lambda_i)$;
--   3. $2 - s_0 \le \max_i \lambda_i < 2 + s_0$ (`spectralTop`);
--   4. $\tfrac1n\sum_i (2+s_0-\lambda_i)^{-1} \le 1$ (`spectralStieltjes`);
--   5. for every $s \in [s_0, 1]$, the empirical Stieltjes transform $\tfrac1n\sum_i(2+s-\lambda_i)^{-1}$ is within $\tfrac1{100}\sqrt s$ of the semicircle value $\tfrac12\bigl(2+s-\sqrt{s(4+s)}\bigr)$ (`semicircleResolvent`);
--   6. $216\,s_0 \le \kappa_n^2$, where $\kappa_n = n^{-7/24}$ (`overlapCentralCutoff`);
--   7. $E(\lambda) + s_0/2 \le 1/1536$. Here $E(\lambda)$ = `saddleSubcriticalError lam` is $\int_0^1 \bigl|\Phi_a'(\lambda) - a/2\bigr|\,da$, with $\Phi_a$ the same infimum at inverse temperature $a$.
--
--   Let $Z_{\mathrm{cube}}(U)$ = `rotatedCubePartition lam 1 U` be the average of $\exp\bigl(\tfrac12\sum_i\lambda_i (Ux)_i^2\bigr)$ over $x \in \{\pm1\}^n$, for an orthogonal matrix $U$. Then
--   $$\int \Bigl(\frac{Z_{\mathrm{cube}}(U)}{Z_{\mathrm{sph}}(\lambda)} - 1\Bigr)^2 \, dU \;\le\; \varepsilon + (n+1)\Bigl(\frac{26\,e\,n}{K}\Bigr)^2 e^{-n\kappa_n^3/24},$$
--   where $dU$ is the Haar probability measure on the orthogonal group (`orthogonalHaar (Fin n)`). In Lean the quantifier over $\lambda, u, v, K, s_0$ also binds an instance `[Nonempty (Fin n)]`.
--
--   All the named functions come from the definitions bundle `OAIQWCSK000` of this split. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.CriticalSK.orientation_normalized_variance_bound`, OpenAI's lemma of that name in `lean/OAI/MathematicalPhysics/CriticalSK/OrientationBounds.lean`.
-- source:
--   OpenAI, Critical slowing down in the Sherrington–Kirkpatrick model, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-slowing-down-in-the-Sherrington-Kirkpatrick-model-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/OrientationBounds.lean (declaration OAI.CriticalSK.orientation_normalized_variance_bound)

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

lemma orientation_normalized_variance_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ [Nonempty (Fin n)] (lam : Fin n → ℝ) (u v : EuclideanSpace ℝ (Fin n)) (K s₀ : ℝ),
      ‖u‖ = Real.sqrt n → ‖v‖ = Real.sqrt n → inner ℝ u v = 0 →
      (∀ i, |lam i| ≤ 3) → 0 < K →
      K*Real.exp ((n:ℝ)*sphericalVariational lam 1) ≤ spherePartition lam 1 (Real.sqrt n) →
      0 ≤ s₀ → spectralTop lam < 2+s₀ → 2-s₀ ≤ spectralTop lam →
      spectralStieltjes lam (2+s₀) ≤ 1 →
      (∀ s ∈ Set.Icc s₀ 1, |spectralStieltjes lam (2+s)-semicircleResolvent s| ≤ (1/100)*Real.sqrt s) →
      216*s₀ ≤ overlapCentralCutoff n^2 →
      saddleSubcriticalError lam+s₀/2 ≤ 1/1536 →
      (∫ U, (rotatedCubePartition lam 1 U / spherePartition lam 1 (Real.sqrt n)-1)^2
        ∂orthogonalHaar (Fin n)) ≤
        ε+(n+1)*((26*Real.exp 1*n/K)^2 * Real.exp (-(n:ℝ)/24*overlapCentralCutoff n^3)) := by
  sorry

end CriticalSK

end

end OAI
end
