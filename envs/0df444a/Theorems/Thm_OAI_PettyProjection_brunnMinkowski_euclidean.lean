-- Prove2me | Theorems.Thm_OAI_PettyProjection_brunnMinkowski_euclidean
-- name    : OAI.PettyProjection.brunnMinkowski_euclidean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:06:19.576498+00:00
-- url     : https://prove2.me/theorems/562ccb47-bab8-4ec7-8d23-bdac7959495a
-- title:
--   Brunn–Minkowski inequality in ℝⁿ for compact convex sets with nonempty interior (concavity form)
-- statement:
--   Let $n \ge 1$ be a natural number and work in $\mathbb R^n$ as `EuclideanSpace ℝ (Fin n)`, with its volume $\mathrm{vol}$ (Mathlib's `volume`, Lebesgue measure) and $\mathrm{vol}(S)$ read as a real number (`volume.real S`, the measure converted to $\mathbb R$). Let $K, M \subseteq \mathbb R^n$ be compact convex sets with nonempty interior (`IsCompact`, `Convex ℝ`, `(interior _).Nonempty`), and let $a, b$ be real numbers with $a \ge 0$, $b \ge 0$ and $a + b = 1$. Then
--   $$a\,\mathrm{vol}(K)^{1/n} + b\,\mathrm{vol}(M)^{1/n} \;\le\; \mathrm{vol}(aK + bM)^{1/n},$$
--   where $aK + bM = \{ax + by : x \in K,\ y \in M\}$ is the pointwise Minkowski combination (`a • K + b • M`) and $t^{1/n}$ is the real power `t ^ ((n:ℝ)⁻¹)`.
--
--   Lean: `OAI.PettyProjection.brunnMinkowski_euclidean`. OpenAI states this as `brunnMinkowski_space : BrunnMinkowskiRoot (Space n) n`, where `Space n` is `EuclideanSpace ℝ (Fin n)` and `BrunnMinkowskiRoot E m` is OpenAI's name for the displayed inequality with exponent $1/m$ (over all such $K, M, a, b$). This statement unfolds both, so it uses only Mathlib. Its proof is OpenAI's proof of `brunnMinkowski_space`.
-- source:
--   H. Brunn, Über Ovale und Eiflächen, Inaugural-Dissertation, München, 1887; H. Minkowski, Geometrie der Zahlen, Teubner, Leipzig, 1896 (the inequality for convex bodies). Proof: OpenAI, Petty's projection-volume conjecture in dimensions at least four, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 088, commit adc7f12, Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/ProjectionBodies/BrunnMinkowski.lean (OpenAI's theorem OAI.PettyProjection.brunnMinkowski_space, restated with its predicate BrunnMinkowskiRoot unfolded)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection

theorem brunnMinkowski_euclidean {n : ℕ} (hn : 0 < n) (K M : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (hcK : Convex ℝ K) (hiK : (interior K).Nonempty)
    (hM : IsCompact M) (hcM : Convex ℝ M) (hiM : (interior M).Nonempty)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * volume.real K ^ ((n:ℝ)⁻¹) + b * volume.real M ^ ((n:ℝ)⁻¹) ≤
      volume.real (a • K + b • M) ^ ((n:ℝ)⁻¹) := by
  sorry

end PettyProjection
end

end OAI
end
