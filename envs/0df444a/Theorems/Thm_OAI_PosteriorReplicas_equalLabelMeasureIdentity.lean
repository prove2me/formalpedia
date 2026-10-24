-- Prove2me | Theorems.Thm_OAI_PosteriorReplicas_equalLabelMeasureIdentity
-- name    : OAI.PosteriorReplicas.equalLabelMeasureIdentity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:30:52.636481+00:00
-- url     : https://prove2.me/theorems/c0d24e18-c87a-405a-acef-746d9cf4b26e
-- title:
--   Finite measure for equal Gaussian labels: the equal-label identity (25) and finiteness (OpenAI posterior replicas, Theorem 3.3)
-- statement:
--   **Notation** (all from the published bundle `Def_PosteriorReplicas`). The base law $P_0$ (`BaseLaw.measure`) is either the uniform probability $\sigma_d$ on the unit sphere of $\mathbb R^d$ or the standard Gaussian $\gamma_d$, and $\nu = f P_0$ for a measurable $f \ge 0$. For a $k \times d$ matrix $A$ (rows `Rows d k`) and labels $y \in \mathbb R^k$:
--   - `baseFiber` is the law of a $P_0$-distributed point conditioned on $Ax = y$, written as an image of the standard Gaussian, and `baseDensity` is the density at $y$ of $Ax$ under $P_0$ (zero unless the rows are linearly independent, and in the spherical case unless the minimal-norm solution of $Ax = y$ has norm below $1$);
--   - $p_A(y)$ (`projectedDensity`) is `baseDensity` times $\int f$ over `baseFiber`;
--   - $\nu_{A,y}$ (`tiltedFiber`) is `baseFiber` reweighted by $f$ and normalized (a Dirac mass when the weight is $0$).
--
--   For a tuple $u = (u_0, \dots, u_m)$ of points, $J(u)$ (`affineVolume`) is the square root of the Gram determinant of the differences $u_i - u_0$, and $F_u$ (`constrainedRows k u`) is the law of a standard Gaussian $k \times d$ matrix whose rows are projected orthogonally onto the complement of the span of those differences. Finally `gaussianRows d k` is the standard Gaussian law $\gamma_{k,d}$ of $A$, and for $H \ge 0$ on triples $(A, y, u)$:
--   $$\mathrm{Left}(H) = \int \gamma_{k,d}(dA) \int_{\mathbb R^k} p_A(y)^{m+1} \int H(A, y, u)\, \nu_{A,y}^{\otimes(m+1)}(du)\, dy \quad (\texttt{equalLabelLeft}),$$
--   $$\mathrm{Right}(H) = (2\pi)^{-km/2} \int J(u)^{-k} \int H(A, Au_0, u)\, F_u(dA)\, \nu^{\otimes(m+1)}(du) \quad (\texttt{equalLabelRight}).$$
--
--   **The statement** (`EqualLabelMeasureIdentity`). For all $d, k, m$ with $k \ge 1$, $m \ge 1$ and $k + m \le d - 2$ (natural-number subtraction), either base law, and every measurable $f \ge 0$ bounded by a finite constant:
--   - $\mathrm{Left}(1) < \infty$;
--   - $\mathrm{Left}(H) = \mathrm{Right}(H)$ for every measurable $H \ge 0$.
--
--   This is the first component of the goal `OAI.PosteriorReplicas.source_main`, and the Lean form of identity (25) of the paper's Theorem 3.3 together with its finiteness.
--
--   Lean: `OAI.PosteriorReplicas.equalLabelMeasureIdentity`, OpenAI's theorem of that name (in `lean/OAI/Probability/PosteriorReplicas/Measures/EqualLabelIdentity.lean`).
-- source:
--   OpenAI, Posterior replicas and conditional information in Gaussian regression, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf, Theorem 3.3; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/PosteriorReplicas/Measures/EqualLabelIdentity.lean (declaration OAI.PosteriorReplicas.equalLabelMeasureIdentity)

import Mathlib
import Definitions.Def_PosteriorReplicas

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
noncomputable section
namespace PosteriorReplicas

theorem equalLabelMeasureIdentity : EqualLabelMeasureIdentity := by
  sorry

end PosteriorReplicas
end

end OAI
end
