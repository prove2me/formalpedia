-- Prove2me | Theorems.Thm_OAI_PosteriorReplicas_replica_log_comparison_ae
-- name    : OAI.PosteriorReplicas.replica_log_comparison_ae
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:34:48.785679+00:00
-- url     : https://prove2.me/theorems/873624d5-9f1d-420c-a2fe-05149e1134f2
-- title:
--   Pointwise comparison of the replica log-likelihood ratio with the observable log-likelihood (OpenAI posterior replicas)
-- statement:
--   **Notation.** Let $\sigma_d$ (`sphereLaw d`) be the uniform probability on the unit sphere of $\mathbb R^d$ and $\nu = f\sigma_d$. For a $k \times d$ matrix $A$ and $y \in \mathbb R^k$, $p_A(y)$ (`projectedDensity .spherical f`) is the density at $y$ of $Ax$ under $\sigma_d$ times the integral of $f$ over the uniform law on the fiber $\{Ax = y\}$ of the sphere. For a tuple $u = (u_0, \dots, u_m)$, $J(u)$ (`affineVolume`) is the square root of the Gram determinant of the differences $u_i - u_0$, and `residualRows u A` replaces each row of $A$ by its component orthogonal to the span of those differences (computed with their Gram matrix).
--   - The reference law $R$ (`equalReference ν`) on triples $z = (A, y, u)$ is the law of $(A', A'u_0, u)$, where $u \sim \nu^{\otimes(m+1)}$, $A$ is an independent standard Gaussian $k \times d$ matrix and $A'$ = `residualRows u A`.
--   - The replica law $Q$ (`replicaLaw .spherical f`) is $R$ with density $(2\pi)^{-km/2} J(u)^{-k} p_A(y)^{-m}$ (`replicaDensity`).
--   - The auxiliary variables $b = (B, E)$ have law `auxLaw d ℓ k`: $B$ is a standard Gaussian $\ell \times d$ matrix and $E$ is an independent standard Gaussian $k \times \ell$ matrix.
--   - `observableRows u b` is the $k \times d$ matrix $CB$, where the rows of $C$ are the Gram–Schmidt orthonormalization of the components of the rows of $E$ orthogonal to the span of the projected differences $B(u_i - u_0)$ (`randomComplement`; the components are computed with the Gram matrix of the projected differences).
--   - `observe (z, b)` is $(b, (Bu_0, \dots, Bu_m))$: what an analyst holding $b$ sees of the tuple.
--
--   **The quantities.** Let $Z$ (`wishartMoment ℓ m k`) be $\mathbb E\bigl[\mathrm{vol}(G)^{-k}\bigr]$ for $m$ independent standard Gaussian vectors $G$ in $\mathbb R^\ell$, where $\mathrm{vol}$ (`gramVolume`) is the square root of the Gram determinant. For $z = (A, y, u)$ and $b = (B, E)$, with $A'' = \texttt{observableRows}\ u\ b$:
--   - the normalized ratio $\mathcal R(z, b)$ (`normalizedRatio`) is $p_{A''}(A'' u_0) \,/\, \bigl(p_A(y)\,\mathrm{vol}(A)\bigr)$;
--   - the projection ratio $\pi(z, b)$ (`projectionGramRatio`) is $\mathrm{vol}\bigl(B(u_1 - u_0), \dots, B(u_m - u_0)\bigr) / J(u)$;
--   - with $\beta = \beta_{k,J} = \mathrm{vol}\{v \in \mathbb R^k : |v| \le 1\}\,(2 + J\,2^k)$ (`binMeanBound`), the envelope (`comparisonEnvelope f J`) is
--   $$\log Z + k \log \pi(z, b) + m \log \mathrm{vol}(A) + m\Bigl(\log \beta + \frac{\mathcal R(z, b)}{\beta} - 1\Bigr).$$
--
--   The observable log-likelihood (`observableLog`) is the logarithm of the observable likelihood $(2\pi)^{-km/2} Z^{-1} J(v)^{-k} p_{CB}\bigl((\langle C_i, v_0\rangle)_i\bigr)^{-m}$ of an observation $(b, v)$, where $C$ is the Gram–Schmidt orthonormalization of the components of the rows of $E$ orthogonal to the span of the differences of $v$. `llr μ ν` is Mathlib's log-likelihood ratio $\log \frac{d\mu}{d\nu}$.
--
--   **The statement.** Let $k, m \ge 1$ with $k + m + 2 \le d$ and $k + m \le \ell$, let $f \ge 0$ be measurable with $f \le L$ for a finite $L$, let $\nu = f\sigma_d$ be a probability measure, and let $J \in \mathbb N$. Then for $(Q \otimes \texttt{auxLaw}\ d\ \ell\ k)$-almost every $(z, b)$,
--   $$\log \frac{d(Q \otimes \texttt{auxLaw})}{d(R \otimes \texttt{auxLaw})}(z, b) \;-\; \texttt{observableLog}\,f\,(\texttt{observe}(z, b)) \;\le\; \texttt{comparisonEnvelope}\,f\,J\,(z, b).$$
--
--   Lean: `OAI.PosteriorReplicas.replica_log_comparison_ae`, OpenAI's lemma of that name (in `lean/OAI/Probability/PosteriorReplicas/Information/ReplicaLoss.lean`). `observableLog`, `comparisonEnvelope`, `normalizedRatio`, `projectionGramRatio`, `binMeanBound`, `wishartMoment`, `observe` and the laws come from the definitions bundle `OAIQWPR000` of this split.
-- source:
--   OpenAI, Posterior replicas and conditional information in Gaussian regression, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/PosteriorReplicas/Information/ReplicaLoss.lean (declaration OAI.PosteriorReplicas.replica_log_comparison_ae)

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

lemma replica_log_comparison_ae {d ℓ k m : ℕ} (hd : k+m+2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k+m ≤ ℓ)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] (J : ℕ) :
    ∀ᵐ z ∂(replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k),
      llr ((replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k))
        ((equalReference ((sphereLaw d).withDensity f)).prod (auxLaw d ℓ k)) z -
        observableLog f (observe z) ≤ comparisonEnvelope f J z := by
  sorry

end PosteriorReplicas
end

end OAI
end
