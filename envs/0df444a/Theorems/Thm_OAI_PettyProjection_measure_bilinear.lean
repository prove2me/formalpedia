-- Prove2me | Theorems.Thm_OAI_PettyProjection_measure_bilinear
-- name    : OAI.PettyProjection.measure_bilinear
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:08:50.786575+00:00
-- url     : https://prove2.me/theorems/f207cff0-b29e-4f48-9c30-940026436b6f
-- title:
--   Bilinear cosine inequality for two measures satisfying the support-functional bounds, n ≥ 4, with its rigidity case (OpenAI Petty projection)
-- statement:
--   Let $n \ge 4$ (with the instance `[NeZero n]`) and let $\mathbb R^n$ be `Space n` (`EuclideanSpace ℝ (Fin n)`) with inner product $\langle\cdot,\cdot\rangle$ and its volume $\mathrm{vol}$ (Lebesgue measure; `volume.real`, the measure as a real number). Let $\kappa_n$ be the volume of the closed unit ball $B$ (`kappa n`, `unitBall n`), and call $K \subseteq \mathbb R^n$ a convex body if it is compact, convex and has nonempty interior (`IsConvexBody K`).
--
--   Definitions used:
--   - The support function of $K$ is $h_K(x) = \sup\{\langle x, y\rangle : y \in K\}$ (`support K x`, Lean's `sSup`). For a measure $\mu$ on $\mathbb R^n$, the support functional is $\int h_K\,d\mu$ (`supportFunctional μ K`, a Bochner integral, $0$ when not integrable).
--   - The normalized volume of $K$ is $\mathrm{vol}(K)^{1/n} / \kappa_n^{1/n}$ (`normalizedVolume K`, with `volumeRoot K` $= \mathrm{vol}(K)^{1/n}$; real powers).
--   - For a measure $\mu$ with $\int \|x\|\,d\mu < \infty$, its cosine seminorm is $y \mapsto \int |\langle x, y\rangle|\,d\mu(x)$ (`cosineSeminorm μ hμ`).
--   - The cosine pairing of measures $\mu, \nu$ is $\int\!\!\int |\langle x, y\rangle|\,d\nu(y)\,d\mu(x)$ (`measurePair μ ν`).
--   - `cosineConstant n` is $2\,\mathrm{mean}\bigl(x \mapsto \max(\langle e_0, x\rangle, 0)\bigr)$, where $\mathrm{mean}$ is the integral against the surface measure of the unit sphere normalized to total mass $1$ (`Spherical.mean`, `Spherical.sigma`) and $e_0$ is the first standard basis vector (`2 * higherKernel 1 (pole n) (fun _ => 1)`).
--
--   Let $\mu, \nu$ be measures on $\mathbb R^n$ such that:
--   - $\int \|x\|\,d\mu(x) < \infty$ and $\int \|x\|\,d\nu(x) < \infty$;
--   - the cosine seminorms of $\mu$ and of $\nu$ are positive at every $y \ne 0$;
--   - for every convex body $M$: normalized volume of $M$ $\le$ support functional of $\mu$ at $M$, and likewise for $\nu$.
--
--   Then `cosineConstant n` $\le$ `measurePair μ ν`. Moreover, if `measurePair μ ν = cosineConstant n`, then there is a continuous linear automorphism $T$ of $\mathbb R^n$ (`Space n ≃L[ℝ] Space n`) such that the support functional of $\mu$ at $T(B)$ equals the normalized volume of $T(B)$.
--
--   Lean: `OAI.PettyProjection.measure_bilinear`, OpenAI's theorem of that name (in `lean/OAI/Geometry/ProjectionBodies/BilinearEquality.lean`). `Space`, `IsConvexBody`, `unitBall` and `kappa` come from the published bundle `Def_PettyProjectionVolume`; `support`, `supportFunctional`, `volumeRoot`, `normalizedVolume`, `cosineSeminorm`, `measurePair`, `Spherical.mean`, `Spherical.sigma`, `Spherical.higherKernel`, `Spherical.pole` and `Spherical.cosineConstant` come from the definitions bundle `OAIQWPP000` of this split.
-- source:
--   OpenAI, Petty's projection-volume conjecture in dimensions at least four, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 088; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/ProjectionBodies/BilinearEquality.lean (declaration OAI.PettyProjection.measure_bilinear)

import Mathlib
import Definitions.Def_PettyProjectionVolume
import Definitions.Def_OAIQWPP000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere mean sigma gaugeMoment cosineConstant)
open RelativeGauge

theorem measure_bilinear {n : ℕ} (hn : 4≤ n) [NeZero n] {μ ν : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hν : Integrable (fun x : Space n => ‖x‖) ν)
    (hqμ : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x)
    (hqν : ∀ x : Space n,x≠0 → 0< cosineSeminorm ν hν x)
    (hbμ : ∀ M : Set (Space n),IsConvexBody M → normalizedVolume M≤ supportFunctional μ M)
    (hbν : ∀ M : Set (Space n),IsConvexBody M → normalizedVolume M≤ supportFunctional ν M) :
    cosineConstant n≤ measurePair μ ν ∧
      (measurePair μ ν=cosineConstant n →
        ∃ T : Space n ≃L[ℝ] Space n,supportFunctional μ (T '' unitBall n)=normalizedVolume (T '' unitBall n)) := by
  sorry

end PettyProjection
end

end OAI
end
