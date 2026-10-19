-- Prove2me | Theorems.Thm_OAI_ContinuumTemperature_convex_pointwise_locally_uniform
-- name    : OAI.ContinuumTemperature.convex_pointwise_locally_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:04:23.728267+00:00
-- url     : https://prove2.me/theorems/265a2f3d-92e8-4940-8314-f804a43e2588
-- title:
--   Rockafellar's theorem — pointwise convergence of convex functions on an open set in finite dimensions is locally uniform
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $S \subseteq E$ an open set, $l$ a filter on an index type $\iota$ with $l \ne \bot$, $F : \iota \to E \to \mathbb R$ and $f : E \to \mathbb R$. Suppose that eventually along $l$ the function $F_i$ is convex on $S$, and that $F_i(x) \to f(x)$ along $l$ for every $x \in S$. Then $F_i \to f$ locally uniformly on $S$ along $l$ (Mathlib's `TendstoLocallyUniformlyOn F f l S`): for every $x \in S$ and every $\varepsilon > 0$ there is a neighbourhood $U$ of $x$ within $S$ such that eventually along $l$, $|F_i(y) - f(y)| < \varepsilon$ for all $y \in U$.
--
--   This is Rockafellar's theorem on limits of convex functions (R. T. Rockafellar, *Convex Analysis*): on an open convex set in $\mathbb R^n$, pointwise convergence of finite convex functions is uniform on compact subsets. In Mathlib, `ConvexOn ℝ S` includes the convexity of $S$, so the hypothesis makes $S$ convex.
--
--   Lean: `OAI.ContinuumTemperature.convex_pointwise_locally_uniform`, OpenAI's theorem of that name (in `lean/OAI/Probability/ContinuumTransition/ConvexUniform.lean`). The statement uses only Mathlib.
-- source:
--   R. T. Rockafellar, Convex Analysis, Princeton University Press, 1970, Theorem 10.8 (the theorem); proof and Lean code: OpenAI, A continuum temperature singularity for a radial pair potential, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-continuum-temperature-singularity-for-a-radial-pair-potential-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ContinuumTransition/ConvexUniform.lean (declaration OAI.ContinuumTemperature.convex_pointwise_locally_uniform)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology NNReal
open Filter Set Metric
noncomputable section
namespace ContinuumTemperature

variable {E : Type u_1} {ι : Type u_2} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {l : Filter ι} [l.NeBot] {S : Set E} {F : ι → E → ℝ} {f : E → ℝ}

theorem convex_pointwise_locally_uniform (hS : IsOpen S)
    (hconv : ∀ᶠ i in l, ConvexOn ℝ S (F i))
    (hlim : ∀ x ∈ S, Tendsto (fun i => F i x) l (𝓝 (f x))) :
    TendstoLocallyUniformlyOn F f l S := by
  sorry

end ContinuumTemperature
end
end

end OAI
end
