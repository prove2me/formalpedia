-- Prove2me | Theorems.Thm_OAI_PosteriorReplicas_equalLabelVersions
-- name    : OAI.PosteriorReplicas.equalLabelVersions
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:31:44.990559+00:00
-- url     : https://prove2.me/theorems/ad63598b-f7d8-4616-87c0-6c617ebca9ce
-- title:
--   Density versions for equal Gaussian labels: the projected density, its ball and Gaussian versions agree (OpenAI posterior replicas, Theorem 3.3)
-- statement:
--   **Notation** (from the published bundle `Def_PosteriorReplicas`). The base law $P_0$ (`BaseLaw.measure`) is the uniform probability on the unit sphere of $\mathbb R^d$ or the standard Gaussian, and $\nu = f P_0$. For a $k \times d$ matrix $A$ and labels $y \in \mathbb R^k$, $p_A(y)$ (`projectedDensity`) is the density at $y$ of $Ax$ under $P_0$ times the integral of $f$ over the conditional law of $P_0$ on $\{Ax = y\}$. Two further versions of it are defined directly from $\nu$, with $|\cdot|$ the Euclidean norm on $\mathbb R^k$ (`labelNorm`):
--   - the ball version (`ballDensityVersion`) is $\liminf_n \nu\{x : |Ax - y| < 1/(n+1)\} \,/\, \mathrm{vol}\{v : |v| < 1/(n+1)\}$;
--   - the Gaussian version (`gaussianDensityVersion`) is $\liminf_n \int \varphi_n(Ax - y)\, \nu(dx)$, with $\varphi_n$ the centered Gaussian density on $\mathbb R^k$ of covariance $(n+1)^{-2} I_k$.
--
--   For a tuple $u = (u_0, \dots, u_m)$, `differences u` are the vectors $u_i - u_0$, and $F_u$ (`constrainedRows k u`) is the law of a standard Gaussian $k \times d$ matrix with its rows projected orthogonally onto the complement of their span. `liftLabel A y` is $\sum_i (G^{-1} y)_i A_i$ with $G$ the Gram matrix of the rows, the minimal-norm solution of $Ax = y$ when the rows are independent.
--
--   **The statement** (`EqualLabelVersions`). For all $d, k, m$ with $k \ge 1$, $m \ge 1$ and $k + m \le d - 2$ (natural-number subtraction), either base law, and every measurable $f \ge 0$ bounded by a finite constant:
--   1. $p_A(y)$, the ball version and the Gaussian version are jointly measurable in $(A, y)$;
--   2. for every $A$ with linearly independent rows, the image of $\nu$ under $x \mapsto Ax$ has density $p_A$ with respect to Lebesgue measure, and $p_A$ agrees with both versions for Lebesgue-almost every $y$;
--   3. for $\nu^{\otimes(m+1)}$-almost every tuple $u$, the differences of $u$ are linearly independent, and for $F_u$-almost every $A$: the rows of $A$ are linearly independent; $Au_i = Au_0$ for all $i$; in the spherical case $|$`liftLabel A (A u₀)`$| < 1$; and $p_A(Au_0)$ is positive, finite, and equal to both versions at $Au_0$.
--
--   This is the second component of the goal `OAI.PosteriorReplicas.source_main`, the Lean form of the paragraph on density versions in the paper's Theorem 3.3.
--
--   Lean: `OAI.PosteriorReplicas.equalLabelVersions`, OpenAI's theorem of that name (in `lean/OAI/Probability/PosteriorReplicas/Measures/EqualLabelVersions.lean`).
-- source:
--   OpenAI, Posterior replicas and conditional information in Gaussian regression, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf, Theorem 3.3; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/PosteriorReplicas/Measures/EqualLabelVersions.lean (declaration OAI.PosteriorReplicas.equalLabelVersions)

import Mathlib
import Definitions.Def_PosteriorReplicas

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace PosteriorReplicas

theorem equalLabelVersions : EqualLabelVersions := by
  sorry

end PosteriorReplicas
end

end OAI
end
