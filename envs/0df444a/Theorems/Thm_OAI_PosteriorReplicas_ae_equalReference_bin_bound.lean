-- Prove2me | Theorems.Thm_OAI_PosteriorReplicas_ae_equalReference_bin_bound
-- name    : OAI.PosteriorReplicas.ae_equalReference_bin_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:33:13.487894+00:00
-- url     : https://prove2.me/theorems/ff1a5a48-ca0b-4957-86ad-18f33d01f413
-- title:
--   Under the equal-label reference law, the expected projected density is at most the dyadic bin envelope (OpenAI posterior replicas)
-- statement:
--   **Notation.** Let $\sigma_d$ (`sphereLaw d`) be the uniform probability on the unit sphere of $\mathbb R^d$ and $\nu = f\sigma_d$. For a $k \times d$ matrix $A$ and $y \in \mathbb R^k$, $p_A(y)$ (`projectedDensity .spherical f`) is the density at $y$ of $Ax$ under $\sigma_d$ times the integral of $f$ over the uniform law on the fiber $\{Ax = y\}$ of the sphere. For a tuple $u = (u_0, \dots, u_m)$:
--   - `residualRows u A` replaces each row of $A$ by its component orthogonal to the span of the differences $u_i - u_0$ (computed with their Gram matrix, so it is the orthogonal projection when the differences are independent);
--   - `expectedDensity f u` is $\mathbb E_A\bigl[p_{A'}(A' u_0)\bigr]$ over a standard Gaussian $k \times d$ matrix $A$, with $A'$ = `residualRows u A`.
--
--   The reference law $R$ (`equalReference ν`) on triples $(A, y, u)$ is the law of $(A', A'u_0, u)$ when $u \sim \nu^{\otimes(m+1)}$ and, independently, $A$ is a standard Gaussian $k \times d$ matrix. For $J \in \mathbb N$ the bin envelope (`binEnvelope ν J A y`) is
--   $$2 + \sum_{j < J} 2^{k(j+1)}\, \nu\bigl\{x : |\ell_A(Ax - y)| \le 2^{-j}\bigr\},$$
--   where $\ell_A(z) = \sum_i (G^{-1} z)_i A_i$ (`liftLabel`, $G$ the Gram matrix of the rows) is the minimal-norm solution of $Ax = z$ when the rows are independent.
--
--   **The statement.** Let $k, m \ge 1$ with $k + m + 2 \le d$, let $f \ge 0$ be measurable with $f \le L$ for a finite $L$, let $\nu$ be a probability measure, and let $J$ satisfy
--   $$L \cdot 72^d \cdot 2^{-J} \cdot (1 + 2^{k+1}) \le 1.$$
--   Then for $R$-almost every $(A, y, u)$,
--   $$\texttt{expectedDensity}\,f\,u \;\le\; \texttt{binEnvelope}\,\nu\,J\,A\,y.$$
--
--   Lean: `OAI.PosteriorReplicas.ae_equalReference_bin_bound`, OpenAI's lemma of that name (in `lean/OAI/Probability/PosteriorReplicas/Geometry/DensityBinEnvelope.lean`). `EqualSpace`, `equalReference`, `expectedDensity` and `binEnvelope` come from the definitions bundle `OAIQWPR000` of this split.
-- source:
--   OpenAI, Posterior replicas and conditional information in Gaussian regression, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/PosteriorReplicas/Geometry/DensityBinEnvelope.lean (declaration OAI.PosteriorReplicas.ae_equalReference_bin_bound)

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

lemma ae_equalReference_bin_bound {d k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] (J : ℕ)
    (hcut : (L*ENNReal.ofReal ((72:ℝ)^d))*ENNReal.ofReal ((1/2:ℝ)^J)*
      (1+(2:ℝ≥0∞)^(k+1)) ≤ 1) :
    ∀ᵐ z : EqualSpace d k m ∂equalReference ((sphereLaw d).withDensity f),
      expectedDensity (k := k) f z.2.2 ≤ binEnvelope ((sphereLaw d).withDensity f) J z.1 z.2.1 := by
  sorry

end PosteriorReplicas
end

end OAI
end
