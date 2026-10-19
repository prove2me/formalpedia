-- Prove2me | Theorems.Thm_OAI_PettyProjection_brunnMinkowski_equality_euclidean
-- name    : OAI.PettyProjection.brunnMinkowski_equality_euclidean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:05:59.616561+00:00
-- url     : https://prove2.me/theorems/cda131ba-f0aa-4fba-9dd6-e2b0357761be
-- title:
--   Equality case of the Brunn–Minkowski inequality in ℝⁿ, n ≥ 2: equality forces homothetic convex bodies
-- statement:
--   Let $n \ge 2$ be a natural number and work in $\mathbb R^n$ as `EuclideanSpace ℝ (Fin n)`, with its volume $\mathrm{vol}$ (Mathlib's `volume`, Lebesgue measure) and $\mathrm{vol}(S)$ read as a real number (`volume.real S`, the measure converted to $\mathbb R$). Let $K, M \subseteq \mathbb R^n$ be compact convex sets with nonempty interior (`IsCompact`, `Convex ℝ`, `(interior _).Nonempty`). Suppose
--   $$\mathrm{vol}(K + M)^{1/n} \;=\; \mathrm{vol}(K)^{1/n} + \mathrm{vol}(M)^{1/n},$$
--   where $K + M$ is the Minkowski sum (pointwise `K + M`) and $t^{1/n}$ is the real power `t ^ ((n:ℝ)⁻¹)`. Then $K$ and $M$ are homothetic: there are a point $z \in \mathbb R^n$ and a real number $c > 0$ with
--   $$K = \{z + c\,x : x \in M\}$$
--   (in Lean, `K = (fun x => z + c • x) '' M`).
--
--   Lean: `OAI.PettyProjection.brunnMinkowski_equality_euclidean`. It uses only Mathlib. OpenAI's `brunnMinkowski_add_equality` states the same over `Space n` (which is `EuclideanSpace ℝ (Fin n)`), with $\mathrm{vol}(S)^{1/n}$ written `volumeRoot S`. This statement unfolds both, and its proof is that theorem.
-- source:
--   H. Brunn, Über Ovale und Eiflächen, Inaugural-Dissertation, München, 1887; H. Minkowski, Geometrie der Zahlen, Teubner, Leipzig, 1896 (the inequality and its equality case for convex bodies). Proof: OpenAI, Petty's projection-volume conjecture in dimensions at least four, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 088, commit adc7f12, Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/ProjectionBodies/Homothety.lean (OpenAI's theorem OAI.PettyProjection.brunnMinkowski_add_equality, restated with its abbreviation volumeRoot unfolded)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection

theorem brunnMinkowski_equality_euclidean {n : ℕ} (hn : 2 ≤ n)
    {K M : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hiK : (interior K).Nonempty) (hM : IsCompact M) (hcM : Convex ℝ M)
    (hiM : (interior M).Nonempty)
    (hv : volume.real (K + M) ^ ((n:ℝ)⁻¹)
      = volume.real K ^ ((n:ℝ)⁻¹) + volume.real M ^ ((n:ℝ)⁻¹)) :
    ∃ z : EuclideanSpace ℝ (Fin n), ∃ c : ℝ, 0 < c ∧ K = (fun x => z + c • x) '' M := by
  sorry

end PettyProjection
end

end OAI
end
