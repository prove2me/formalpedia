-- Prove2me | Theorems.Thm_OAI_PosteriorReplicas_observableLikelihood_lintegral
-- name    : OAI.PosteriorReplicas.observableLikelihood_lintegral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:34:23.272318+00:00
-- url     : https://prove2.me/theorems/61716290-e1ff-4e2f-a417-c176fa604aaa
-- title:
--   The observable projected likelihood integrates to one under the reference law (OpenAI posterior replicas, cf. Lemma 4.1)
-- statement:
--   **Notation.** Let $\sigma_d$ (`sphereLaw d`) be the uniform probability on the unit sphere of $\mathbb R^d$ and $\nu = f\sigma_d$. For a $k \times d$ matrix $A$ and $y \in \mathbb R^k$, $p_A(y)$ (`projectedDensity .spherical f`) is the density at $y$ of $Ax$ under $\sigma_d$ times the integral of $f$ over the uniform law on the fiber $\{Ax = y\}$ of the sphere. For a tuple $u = (u_0, \dots, u_m)$, $J(u)$ (`affineVolume`) is the square root of the Gram determinant of the differences $u_i - u_0$, and `residualRows u A` replaces each row of $A$ by its component orthogonal to the span of those differences (computed with their Gram matrix).
--   - The reference law $R$ (`equalReference ν`) on triples $z = (A, y, u)$ is the law of $(A', A'u_0, u)$, where $u \sim \nu^{\otimes(m+1)}$, $A$ is an independent standard Gaussian $k \times d$ matrix and $A'$ = `residualRows u A`.
--   - The replica law $Q$ (`replicaLaw .spherical f`) is $R$ with density $(2\pi)^{-km/2} J(u)^{-k} p_A(y)^{-m}$ (`replicaDensity`).
--   - The auxiliary variables $b = (B, E)$ have law `auxLaw d ℓ k`: $B$ is a standard Gaussian $\ell \times d$ matrix and $E$ is an independent standard Gaussian $k \times \ell$ matrix.
--   - `observableRows u b` is the $k \times d$ matrix $CB$, where the rows of $C$ are the Gram–Schmidt orthonormalization of the components of the rows of $E$ orthogonal to the span of the projected differences $B(u_i - u_0)$ (`randomComplement`; the components are computed with the Gram matrix of the projected differences).
--   - `observe (z, b)` is $(b, (Bu_0, \dots, Bu_m))$: what an analyst holding $b$ sees of the tuple.
--
--   **The observable likelihood.** Let $Z$ (`wishartMoment ℓ m k`) be $\mathbb E\bigl[\mathrm{vol}(G)^{-k}\bigr]$, where $G$ consists of $m$ independent standard Gaussian vectors in $\mathbb R^\ell$ and $\mathrm{vol}(G)$ (`gramVolume`) is the square root of their Gram determinant. For an observation $(b, v)$ with $b = (B, E)$ and $v = (v_0, \dots, v_m)$ a tuple in $\mathbb R^\ell$, let $C$ be the Gram–Schmidt orthonormalization of the components of the rows of $E$ orthogonal to the span of the differences $v_i - v_0$ (`randomComplement`). Then `observableLikelihood f (b, v)` is
--   $$(2\pi)^{-km/2}\, Z^{-1}\, J(v)^{-k}\, p_{CB}\bigl((\langle C_i, v_0\rangle)_i\bigr)^{-m}.$$
--   It depends only on what `observe` reveals.
--
--   **The statement.** Let $k, m \ge 1$ with $k + m + 2 \le d$ and $k + m \le \ell$, let $f \ge 0$ be measurable with $f \le L$ for a finite $L$, and let $\nu = f\sigma_d$ be a probability measure. Then
--   $$\int \texttt{observableLikelihood}\,f\,(\texttt{observe}(z, b))\; (R \otimes \texttt{auxLaw}\ d\ \ell\ k)(dz, db) \;=\; 1.$$
--
--   Lean: `OAI.PosteriorReplicas.observableLikelihood_lintegral`, OpenAI's lemma of that name (in `lean/OAI/Probability/PosteriorReplicas/Information/ObservableLikelihood.lean`). `equalReference`, `auxLaw`, `observe`, `observableLikelihood`, `wishartMoment` and `randomComplement` come from the definitions bundle `OAIQWPR000` of this split.
-- source:
--   OpenAI, Posterior replicas and conditional information in Gaussian regression, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf, cf. Lemma 4.1; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/PosteriorReplicas/Information/ObservableLikelihood.lean (declaration OAI.PosteriorReplicas.observableLikelihood_lintegral)

import Mathlib
import Definitions.Def_PosteriorReplicas
import Definitions.Def_OAIQWPR000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma observableLikelihood_lintegral {d ℓ k m : ℕ} (hd : k+m+2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k+m ≤ ℓ)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] :
    (∫⁻ z : EqualSpace d k m × AuxSpace d ℓ k, observableLikelihood f (observe z)
      ∂(equalReference ((sphereLaw d).withDensity f)).prod (auxLaw d ℓ k)) = 1 := by
  sorry

end PosteriorReplicas
end

end OAI
end
