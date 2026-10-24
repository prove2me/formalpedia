-- Prove2me | Theorems.Thm_OAI_PosteriorReplicas_ae_expectedDensity_le_inverse
-- name    : OAI.PosteriorReplicas.ae_expectedDensity_le_inverse
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:33:12.140067+00:00
-- url     : https://prove2.me/theorems/711adaff-bae3-41c8-b51a-bb1b70dd175c
-- title:
--   The expected projected density at a tuple is at most the ν-average of the inverse k-th power of the distance to its affine span (OpenAI posterior replicas)
-- statement:
--   **Notation.** Let $\sigma_d$ (`sphereLaw d`) be the uniform probability on the unit sphere of $\mathbb R^d$ and $\nu = f\sigma_d$. For a $k \times d$ matrix $A$ and $y \in \mathbb R^k$, $p_A(y)$ (`projectedDensity .spherical f`) is the density at $y$ of $Ax$ under $\sigma_d$ times the integral of $f$ over the uniform law on the fiber $\{x \in S^{d-1} : Ax = y\}$; it is the density of the image of $\nu$ under $x \mapsto Ax$ when the rows of $A$ are independent. For a tuple $u = (u_0, \dots, u_m)$ of points of $\mathbb R^d$:
--   - `residualRows u A` replaces each row $A_j$ by $A_j - \sum_i (G^{-1} c)_i (u_i - u_0)$, where $G$ is the Gram matrix of the differences $u_i - u_0$ and $c_i = \langle u_i - u_0, A_j\rangle$; when the differences are linearly independent this is the orthogonal projection of $A_j$ onto the complement of their span;
--   - `expectedDensity f u` is $\mathbb E_A\bigl[p_{A'}(A' u_0)\bigr]$, with $A$ a standard Gaussian $k \times d$ matrix and $A'$ = `residualRows u A`;
--   - `tupleDistance u x` is the norm of the orthogonal projection of $x - u_0$ onto the complement of the span of the differences, the distance from $x$ to the affine span of $u$.
--
--   **The statement.** Let $k, m \ge 1$ with $k + m + 2 \le d$, and let $f \ge 0$ be measurable with $f \le L$ for a finite $L$. Then for $\nu^{\otimes(m+1)}$-almost every tuple $u$,
--   $$\texttt{expectedDensity}\,f\,u \;\le\; \int \mathrm{dist}(x, \mathrm{aff}\,u)^{-k}\, \nu(dx).$$
--   (The integrand is `ENNReal.ofReal` of the real power, so it is $0$ where the real inverse is $0$.)
--
--   Lean: `OAI.PosteriorReplicas.ae_expectedDensity_le_inverse`, OpenAI's lemma of that name (in `lean/OAI/Probability/PosteriorReplicas/Geometry/DensityBinEnvelope.lean`). `expectedDensity`, `residualRows` and `tupleDistance` come from the definitions bundle `OAIQWPR000` of this split.
-- source:
--   OpenAI, Posterior replicas and conditional information in Gaussian regression, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/PosteriorReplicas/Geometry/DensityBinEnvelope.lean (declaration OAI.PosteriorReplicas.ae_expectedDensity_le_inverse)

import Mathlib
import Definitions.Def_PosteriorReplicas
import Definitions.Def_OAIQWPR000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma ae_expectedDensity_le_inverse {d k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    ∀ᵐ u : Tuple d m ∂Measure.pi (fun _ => (sphereLaw d).withDensity f),
      expectedDensity (k := k) f u ≤ ∫⁻ x, ENNReal.ofReal ((tupleDistance u x)⁻¹^k)
        ∂(sphereLaw d).withDensity f := by
  sorry

end PosteriorReplicas
end

end OAI
end
