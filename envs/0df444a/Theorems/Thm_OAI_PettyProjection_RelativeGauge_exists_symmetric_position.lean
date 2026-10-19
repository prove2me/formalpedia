-- Prove2me | Theorems.Thm_OAI_PettyProjection_RelativeGauge_exists_symmetric_position
-- name    : OAI.PettyProjection.RelativeGauge.exists_symmetric_position
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:08:42.698508+00:00
-- url     : https://prove2.me/theorems/c121ba15-72dc-4cd7-8272-45e2efe3f669
-- title:
--   A cosine-spanning measure on ℝⁿ has a symmetric linear position with a variational minimizing gauge whose moment field vanishes (OpenAI Petty projection)
-- statement:
--   Let $n \ge 1$ (`[NeZero n]`) and let $\mathbb R^n$ be `Space n` (`EuclideanSpace ℝ (Fin n)`) with inner product $\langle\cdot,\cdot\rangle$. Let $S^{n-1}$ be its unit sphere (`Spherical.Sphere n`) and $\sigma$ the surface measure on it normalized to total mass $1$ (`Spherical.sigma n`, Mathlib's `volume.toSphere` divided by its total mass). Write $\mathrm{mean}(h) = \int h\,d\sigma$ (`Spherical.mean`).
--
--   Let $\mu$ be a measure on $\mathbb R^n$ with $\int \|x\|\,d\mu(x) < \infty$ (`Integrable (fun x => ‖x‖) μ`). Its cosine seminorm is $y \mapsto \int |\langle x, y\rangle|\,d\mu(x)$ (`cosineSeminorm μ hμ`). Assume it is positive at every $y \ne 0$.
--
--   Definitions used in the conclusion:
--   - A `RelativeGauge ⊤` is a seminorm $g$ on $\mathbb R^n$ (`toSeminorm`) together with a constant $c > 0$ such that $c\|x\| \le g(x)$ for all $x$. (The structure also requires $g(Px) = g(x)$ for the orthogonal projection $P$ onto the whole space, which holds trivially.) Its body is $\{x : g(x) \le 1\}$ (`body`).
--   - The support function of a set $K$ is $h_K(x) = \sup\{\langle x, y\rangle : y \in K\}$ (`support K x`, Lean's `sSup`). The support functional of $\mu$ at $K$ is $\int h_K\,d\mu$ (`supportFunctional μ K`).
--   - `regime n` is `true` exactly when $n = 4$. The objective of a seminorm $g$ is $\mathrm{mean}(u \mapsto \log g(u))$ when the flag is `true` and $\mathrm{mean}(u \mapsto g(u))$ when it is `false` (`Spherical.objective`; `Real.log`, with $\log 0 = 0$).
--   - `IsMinimizer ν b g` means: the support functional of $\nu$ at the body of $g$ equals $1$, and the objective (with flag $b$) of $g$ is at most that of every relative gauge $q$ whose body also has support functional $1$ for $\nu$.
--   - For a seminorm $g$ and $k \in \mathbb N$, `Position.momentField g k` is the $n \times n$ array (an element of `EuclideanSpace ℝ (Fin n × Fin n)`) with entries
--   $$\frac{\mathrm{mean}\bigl(u \mapsto g(u)^k\,u_i\,u_j\bigr)}{\mathrm{mean}\bigl(u \mapsto g(u)^k\bigr)} - \frac{\delta_{ij}}{n}.$$
--   - `Scalar.exponent n` is $1$ if $n = 4$ and $2$ otherwise.
--
--   Then there is a continuous linear automorphism $T$ of $\mathbb R^n$ (`Space n ≃L[ℝ] Space n`) that is self-adjoint (`T.toLinearMap.IsSymmetric`), and a relative gauge $g$ with `IsMinimizer (μ.map T) (regime n) g`, where `μ.map T` is the pushforward of $\mu$ under $T$, and with `momentField g (exponent n) = 0`.
--
--   Lean: `OAI.PettyProjection.RelativeGauge.exists_symmetric_position`, OpenAI's theorem of that name (in `lean/OAI/Geometry/ProjectionBodies/AffinePosition.lean`). `Space` comes from the published bundle `Def_PettyProjectionVolume`; `Spherical.Sphere`, `Spherical.sigma`, `Spherical.mean`, `Spherical.objective`, `cosineSeminorm`, `RelativeGauge`, `RelativeGauge.body`, `support`, `supportFunctional`, `RelativeGauge.IsMinimizer`, `regime`, `Position.momentField` and `Scalar.exponent` come from the definitions bundle `OAIQWPP000` of this split.
-- source:
--   OpenAI, Petty's projection-volume conjecture in dimensions at least four, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 088; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/ProjectionBodies/AffinePosition.lean (declaration OAI.PettyProjection.RelativeGauge.exists_symmetric_position)

import Mathlib
import Definitions.Def_PettyProjectionVolume
import Definitions.Def_OAIQWPP000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection
namespace RelativeGauge
variable {n : ℕ} [NeZero n]

theorem exists_symmetric_position {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0 < cosineSeminorm μ hμ x) :
    ∃ T : Space n ≃L[ℝ] Space n,T.toLinearMap.IsSymmetric ∧
      ∃ g : RelativeGauge (⊤ : Submodule ℝ (Space n)),IsMinimizer (μ.map T) (regime n) g ∧
        Position.momentField g.toSeminorm (Scalar.exponent n)=0 := by
  sorry

end RelativeGauge
end PettyProjection
end

end OAI
end
