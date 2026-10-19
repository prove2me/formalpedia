-- Prove2me | Theorems.Thm_OAI_PettyProjection_Spherical_norm_estimate
-- name    : OAI.PettyProjection.Spherical.norm_estimate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:08:47.285353+00:00
-- url     : https://prove2.me/theorems/dd59b133-b75d-4f69-8f8b-6053993a857f
-- title:
--   Spherical energy estimate for a norm with mean of g^(-n) equal to 1, n ≥ 4, with equality only for the Euclidean norm (OpenAI Petty projection)
-- statement:
--   Let $n \ge 4$ (with the instance `[NeZero n]`) and let $\mathbb R^n$ be `Spherical.Space n` (`EuclideanSpace ℝ (Fin n)`). Let $S^{n-1}$ be its unit sphere (`Sphere n`) and $\sigma$ the surface measure on it normalized to total mass $1$ (`sigma n`, Mathlib's `volume.toSphere` divided by its total mass). Write $\mathrm{mean}(h) = \int h\,d\sigma$ (`mean`).
--
--   Let $L^2(\sigma)$ be the real Hilbert space `Lp ℝ 2 (sigma n)` (`H n`), and let `toH n` send a continuous function on $S^{n-1}$ to its class in $L^2(\sigma)$. Let $V \subseteq L^2(\sigma)$ be the span of the restrictions to $S^{n-1}$ of the coordinate products $x_i x_j$ ($1 \le i, j \le n$) (`lowSpace n`). Let $Q$ be the orthogonal projection of $L^2(\sigma)$ onto $V^\perp$ (`Q n`, Mathlib's `starProjection` of `(lowSpace n)ᗮ`).
--
--   Put $k = $ `Scalar.exponent n`, which is $1$ if $n = 4$ and $2$ otherwise, and let $c_n = $ `Scalar.coefficient n`, which is $121/35$ if $n = 4$ and $(n^2 + 5n + 7)/((n+1)(n+3))$ otherwise.
--
--   Let $g$ be a seminorm on $\mathbb R^n$ (`Seminorm ℝ (Space n)`) with $g(u) > 0$ for every $u \in S^{n-1}$ and $\mathrm{mean}(u \mapsto g(u)^{-n}) = 1$. Let $G_k$ be the restriction of $x \mapsto g(x)^k$ to $S^{n-1}$, a continuous function (`restrictContinuous (fun x => g x ^ exponent n) ((seminorm_continuous n g).pow _)`; `seminorm_continuous n g` is the bundle's proof that $g$ is continuous). Then
--   $$c_n\,\bigl\|Q\,G_k\bigr\|_{L^2(\sigma)}^2 \;\le\; \mathrm{mean}\bigl(g^k\bigr)^2 - \mathrm{mean}\bigl(g^{k-1}\bigr)^2,$$
--   where $g^k$ and $g^{k-1}$ are the functions $u \mapsto g(u)^k$ and $u \mapsto g(u)^{k-1}$ on $S^{n-1}$ (natural-number powers, $k - 1$ natural subtraction). Moreover, equality holds if and only if $g(u) = 1$ for every $u \in S^{n-1}$.
--
--   Lean: `OAI.PettyProjection.Spherical.norm_estimate`, OpenAI's theorem of that name (in `lean/OAI/Geometry/ProjectionBodies/NormEstimates.lean`). `Spherical.Space`, `Sphere`, `sigma`, `mean`, `H`, `toH`, `lowSpace`, `Q`, `restrictContinuous`, `seminorm_continuous`, `Scalar.exponent` and `Scalar.coefficient` come from the definitions bundle `OAIQWPP000` of this split.
-- source:
--   OpenAI, Petty's projection-volume conjecture in dimensions at least four, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 088; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/ProjectionBodies/NormEstimates.lean (declaration OAI.PettyProjection.Spherical.norm_estimate)

import Mathlib
import Definitions.Def_PettyProjectionVolume
import Definitions.Def_OAIQWPP000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical
open Scalar

theorem norm_estimate {n : ℕ} (hn : 4 ≤ n) [NeZero n]
    (g : Seminorm ℝ (Space n)) (hg : ∀ u : Sphere n, 0 < g u)
    (hnorm : mean (fun u : Sphere n => (g u)⁻¹^n) = 1) :
    coefficient n * ‖Q n (toH n (restrictContinuous (fun x => g x ^ exponent n)
      ((seminorm_continuous n g).pow _)))‖^2 ≤
      (mean (fun u : Sphere n => (g u)^exponent n))^2 -
        (mean (fun u : Sphere n => (g u)^(exponent n-1)))^2 ∧
    (coefficient n * ‖Q n (toH n (restrictContinuous (fun x => g x ^ exponent n)
      ((seminorm_continuous n g).pow _)))‖^2 =
      (mean (fun u : Sphere n => (g u)^exponent n))^2 -
        (mean (fun u : Sphere n => (g u)^(exponent n-1)))^2 ↔ ∀ u : Sphere n, g u = 1) := by
  sorry

end PettyProjection.Spherical
end

end OAI
end
