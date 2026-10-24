-- Prove2me | Theorems.Thm_OAI_PosteriorReplicas_replica_klDiv_ne_top
-- name    : OAI.PosteriorReplicas.replica_klDiv_ne_top
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:35:35.712235+00:00
-- url     : https://prove2.me/theorems/a8dbd314-e7bd-4ef0-8df4-1019d777b398
-- title:
--   The replica law has finite relative entropy from the equal-label reference law (OpenAI posterior replicas, cf. Lemma 3.6)
-- statement:
--   **Notation.** Let $\sigma_d$ (`sphereLaw d`) be the uniform probability on the unit sphere of $\mathbb R^d$ and $\nu = f\sigma_d$. For a $k \times d$ matrix $A$ and $y \in \mathbb R^k$, $p_A(y)$ (`projectedDensity .spherical f`) is the density at $y$ of $Ax$ under $\sigma_d$ times the integral of $f$ over the uniform law on the fiber $\{Ax = y\}$ of the sphere. For a tuple $u = (u_0, \dots, u_m)$, $J(u)$ (`affineVolume`) is the square root of the Gram determinant of the differences $u_i - u_0$, and `residualRows u A` replaces each row of $A$ by its component orthogonal to the span of those differences (computed with their Gram matrix).
--   - The reference law $R$ (`equalReference ν`) on triples $z = (A, y, u)$ is the law of $(A', A'u_0, u)$, where $u \sim \nu^{\otimes(m+1)}$, $A$ is an independent standard Gaussian $k \times d$ matrix and $A'$ = `residualRows u A`.
--   - The replica law $Q$ (`replicaLaw .spherical f`) is $R$ with density $(2\pi)^{-km/2} J(u)^{-k} p_A(y)^{-m}$ (`replicaDensity`).
--   - The auxiliary variables $b = (B, E)$ have law `auxLaw d ℓ k`: $B$ is a standard Gaussian $\ell \times d$ matrix and $E$ is an independent standard Gaussian $k \times \ell$ matrix.
--   - `observableRows u b` is the $k \times d$ matrix $CB$, where the rows of $C$ are the Gram–Schmidt orthonormalization of the components of the rows of $E$ orthogonal to the span of the projected differences $B(u_i - u_0)$ (`randomComplement`; the components are computed with the Gram matrix of the projected differences).
--   - `observe (z, b)` is $(b, (Bu_0, \dots, Bu_m))$: what an analyst holding $b$ sees of the tuple.
--
--   **The statement.** Let $k, m \ge 1$ with $4k + m + 2 \le d$, let $f \ge 0$ be measurable with $f \le L$ for a finite $L$, and let $\nu = f\sigma_d$ be a probability measure. Then the relative entropy (`klDiv`) of $Q$ from $R$ is finite:
--   $$D(Q \,\|\, R) < \infty.$$
--
--   Lean: `OAI.PosteriorReplicas.replica_klDiv_ne_top`, OpenAI's lemma of that name (in `lean/OAI/Probability/PosteriorReplicas/Information/ReplicaFiniteKL.lean`). `equalReference` and `replicaLaw` come from the definitions bundle `OAIQWPR000` of this split.
-- source:
--   OpenAI, Posterior replicas and conditional information in Gaussian regression, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf, cf. Lemma 3.6; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/PosteriorReplicas/Information/ReplicaFiniteKL.lean (declaration OAI.PosteriorReplicas.replica_klDiv_ne_top)

import Mathlib
import Definitions.Def_PosteriorReplicas
import Definitions.Def_OAIQWPR000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma replica_klDiv_ne_top {d k m : ℕ} (hd : 4*k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] :
    klDiv (replicaLaw (k := k) (m := m) .spherical f)
      (equalReference ((sphereLaw d).withDensity f)) ≠ ∞ := by
  sorry

end PosteriorReplicas
end

end OAI
end
