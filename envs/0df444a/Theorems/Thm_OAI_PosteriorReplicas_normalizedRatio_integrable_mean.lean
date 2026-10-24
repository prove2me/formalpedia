-- Prove2me | Theorems.Thm_OAI_PosteriorReplicas_normalizedRatio_integrable_mean
-- name    : OAI.PosteriorReplicas.normalizedRatio_integrable_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:34:23.624003+00:00
-- url     : https://prove2.me/theorems/85a51702-0255-4bc3-9846-f5161ee179d7
-- title:
--   The normalized projected-density ratio is integrable under the replica law, with mean at most vol(B^k)(2 + J 2^k) (OpenAI posterior replicas, cf. Lemma 4.2)
-- statement:
--   **Notation.** Let $\sigma_d$ (`sphereLaw d`) be the uniform probability on the unit sphere of $\mathbb R^d$ and $\nu = f\sigma_d$. For a $k \times d$ matrix $A$ and $y \in \mathbb R^k$, $p_A(y)$ (`projectedDensity .spherical f`) is the density at $y$ of $Ax$ under $\sigma_d$ times the integral of $f$ over the uniform law on the fiber $\{Ax = y\}$ of the sphere. For a tuple $u = (u_0, \dots, u_m)$, $J(u)$ (`affineVolume`) is the square root of the Gram determinant of the differences $u_i - u_0$, and `residualRows u A` replaces each row of $A$ by its component orthogonal to the span of those differences (computed with their Gram matrix).
--   - The reference law $R$ (`equalReference ν`) on triples $z = (A, y, u)$ is the law of $(A', A'u_0, u)$, where $u \sim \nu^{\otimes(m+1)}$, $A$ is an independent standard Gaussian $k \times d$ matrix and $A'$ = `residualRows u A`.
--   - The replica law $Q$ (`replicaLaw .spherical f`) is $R$ with density $(2\pi)^{-km/2} J(u)^{-k} p_A(y)^{-m}$ (`replicaDensity`).
--   - The auxiliary variables $b = (B, E)$ have law `auxLaw d ℓ k`: $B$ is a standard Gaussian $\ell \times d$ matrix and $E$ is an independent standard Gaussian $k \times \ell$ matrix.
--   - `observableRows u b` is the $k \times d$ matrix $CB$, where the rows of $C$ are the Gram–Schmidt orthonormalization of the components of the rows of $E$ orthogonal to the span of the projected differences $B(u_i - u_0)$ (`randomComplement`; the components are computed with the Gram matrix of the projected differences).
--   - `observe (z, b)` is $(b, (Bu_0, \dots, Bu_m))$: what an analyst holding $b$ sees of the tuple.
--
--   **The ratio.** For $z = (A, y, u)$ and auxiliary $b$, with $A'' = \texttt{observableRows}\ u\ b$ and $\mathrm{vol}(A)$ (`gramVolume`) the square root of the Gram determinant of the rows of $A$, the normalized ratio (`normalizedRatio f (z, b)`) is
--   $$\mathcal R(z, b) = \frac{p_{A''}(A'' u_0)}{p_A(y)\,\mathrm{vol}(A)},$$
--   computed in $[0, \infty]$. For $J \in \mathbb N$ let $\beta_{k,J} = \mathrm{vol}\{v \in \mathbb R^k : |v| \le 1\}\,(2 + J\,2^k)$ (`binMeanBound k J`).
--
--   **The statement.** Let $k, m \ge 1$ with $k + m + 2 \le d$ and $k + m \le \ell$, let $f \ge 0$ be measurable with $f \le L$ for a finite $L$, let $\nu = f\sigma_d$ be a probability measure, and let $J$ satisfy
--   $$L \cdot 72^d \cdot 2^{-J} \cdot (1 + 2^{k+1}) \le 1.$$
--   Then $\mathcal R$, converted to a real number (`ENNReal.toReal`, which sends $\infty$ to $0$), is integrable for $Q \otimes \texttt{auxLaw}\ d\ \ell\ k$, and
--   $$\int \mathcal R \; d(Q \otimes \texttt{auxLaw}\ d\ \ell\ k) \;\le\; \beta_{k,J}.$$
--
--   Lean: `OAI.PosteriorReplicas.normalizedRatio_integrable_mean`, OpenAI's lemma of that name (in `lean/OAI/Probability/PosteriorReplicas/Information/ReplicaLoss.lean`). `normalizedRatio`, `binMeanBound`, `gramVolume`, `replicaLaw`, `auxLaw` and `observableRows` come from the definitions bundle `OAIQWPR000` of this split.
-- source:
--   OpenAI, Posterior replicas and conditional information in Gaussian regression, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf, cf. Lemma 4.2; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/PosteriorReplicas/Information/ReplicaLoss.lean (declaration OAI.PosteriorReplicas.normalizedRatio_integrable_mean)

import Mathlib
import Definitions.Def_PosteriorReplicas
import Definitions.Def_OAIQWPR000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Matrix InnerProductSpace Filter Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma normalizedRatio_integrable_mean {d ℓ k m : ℕ} (hd : k+m+2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k+m ≤ ℓ)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] (J : ℕ)
    (hcut : (L*ENNReal.ofReal ((72:ℝ)^d))*ENNReal.ofReal ((1/2:ℝ)^J)*
      (1+(2:ℝ≥0∞)^(k+1)) ≤ 1) :
    Integrable (fun z => (normalizedRatio f z).toReal)
      ((replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k)) ∧
    (∫ z, (normalizedRatio f z).toReal
      ∂(replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k)) ≤ binMeanBound k J := by
  sorry

end PosteriorReplicas
end

end OAI
end
