-- Prove2me | Theorems.Thm_OAI_PosteriorReplicas_replica_lifted_loss
-- name    : OAI.PosteriorReplicas.replica_lifted_loss
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:34:50.884081+00:00
-- url     : https://prove2.me/theorems/4147a5f8-7921-4ce8-a7cb-422236c2cffd
-- title:
--   The replica correlation drops by at most the comparison cost after the auxiliary projection (OpenAI posterior replicas)
-- statement:
--   **Notation.** Let $\sigma_d$ (`sphereLaw d`) be the uniform probability on the unit sphere of $\mathbb R^d$ and $\nu = f\sigma_d$. For a $k \times d$ matrix $A$ and $y \in \mathbb R^k$, $p_A(y)$ (`projectedDensity .spherical f`) is the density at $y$ of $Ax$ under $\sigma_d$ times the integral of $f$ over the uniform law on the fiber $\{Ax = y\}$ of the sphere. For a tuple $u = (u_0, \dots, u_m)$, $J(u)$ (`affineVolume`) is the square root of the Gram determinant of the differences $u_i - u_0$, and `residualRows u A` replaces each row of $A$ by its component orthogonal to the span of those differences (computed with their Gram matrix).
--   - The reference law $R$ (`equalReference ν`) on triples $z = (A, y, u)$ is the law of $(A', A'u_0, u)$, where $u \sim \nu^{\otimes(m+1)}$, $A$ is an independent standard Gaussian $k \times d$ matrix and $A'$ = `residualRows u A`.
--   - The replica law $Q$ (`replicaLaw .spherical f`) is $R$ with density $(2\pi)^{-km/2} J(u)^{-k} p_A(y)^{-m}$ (`replicaDensity`).
--   - The auxiliary variables $b = (B, E)$ have law `auxLaw d ℓ k`: $B$ is a standard Gaussian $\ell \times d$ matrix and $E$ is an independent standard Gaussian $k \times \ell$ matrix.
--   - `observableRows u b` is the $k \times d$ matrix $CB$, where the rows of $C$ are the Gram–Schmidt orthonormalization of the components of the rows of $E$ orthogonal to the span of the projected differences $B(u_i - u_0)$ (`randomComplement`; the components are computed with the Gram matrix of the projected differences).
--   - `observe (z, b)` is $(b, (Bu_0, \dots, Bu_m))$: what an analyst holding $b$ sees of the tuple.
--
--   **The cost.** Let $Z$ (`wishartMoment ℓ m k`) be $\mathbb E\bigl[\mathrm{vol}(G)^{-k}\bigr]$ for $m$ independent standard Gaussian vectors $G$ in $\mathbb R^\ell$, where $\mathrm{vol}$ is the square root of the Gram determinant, and let $\beta_{k,J} = \mathrm{vol}\{v \in \mathbb R^k : |v| \le 1\}\,(2 + J\,2^k)$ (`binMeanBound`). The comparison cost (`comparisonCost d ℓ k m J`) is
--   $$\log Z + k\,\frac{m}{2}\log(\ell + 1) + m\,\frac{k}{2}\log(d + 1) + m \log \beta_{k,J}.$$
--
--   **The statement.** Let $k, m \ge 1$ with $4k + m + 2 \le d$ and $k + m \le \ell$, let $f \ge 0$ be measurable with $f \le L$ for a finite $L$, let $\nu = f\sigma_d$ be a probability measure, and let $J$ satisfy
--   $$L \cdot 72^d \cdot 2^{-J} \cdot (1 + 2^{k+1}) \le 1.$$
--   Write $\mathrm{obs}_\ast$ for the image under `observe`. Then, with both relative entropies converted to real numbers (`ENNReal.toReal`, which sends $\infty$ to $0$),
--   $$D(Q \,\|\, R) \;\le\; D\bigl(\mathrm{obs}_\ast(Q \otimes \texttt{auxLaw}\ d\ \ell\ k) \,\big\|\, \mathrm{obs}_\ast(R \otimes \texttt{auxLaw}\ d\ \ell\ k)\bigr) + \texttt{comparisonCost}\ d\ \ell\ k\ m\ J.$$
--
--   Lean: `OAI.PosteriorReplicas.replica_lifted_loss`, OpenAI's lemma of that name (in `lean/OAI/Probability/PosteriorReplicas/Information/ReplicaLoss.lean`). `comparisonCost`, `binMeanBound`, `wishartMoment`, `observe` and the laws come from the definitions bundle `OAIQWPR000` of this split.
-- source:
--   OpenAI, Posterior replicas and conditional information in Gaussian regression, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/PosteriorReplicas/Information/ReplicaLoss.lean (declaration OAI.PosteriorReplicas.replica_lifted_loss)

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

lemma replica_lifted_loss {d ℓ k m : ℕ} (hd : 4*k+m+2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k+m ≤ ℓ)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] (J : ℕ)
    (hcut : (L*ENNReal.ofReal ((72:ℝ)^d))*ENNReal.ofReal ((1/2:ℝ)^J)*
      (1+(2:ℝ≥0∞)^(k+1)) ≤ 1) :
    (klDiv (replicaLaw (k := k) (m := m) .spherical f) (equalReference ((sphereLaw d).withDensity f))).toReal ≤
      (klDiv (((replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k)).map observe)
        (((equalReference ((sphereLaw d).withDensity f)).prod (auxLaw d ℓ k)).map observe)).toReal +
      comparisonCost d ℓ k m J := by
  sorry

end PosteriorReplicas
end

end OAI
end
