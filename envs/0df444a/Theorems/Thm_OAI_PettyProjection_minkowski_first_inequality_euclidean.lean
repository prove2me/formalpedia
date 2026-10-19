-- Prove2me | Theorems.Thm_OAI_PettyProjection_minkowski_first_inequality_euclidean
-- name    : OAI.PettyProjection.minkowski_first_inequality_euclidean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:06:22.541886+00:00
-- url     : https://prove2.me/theorems/b2427fbf-08f1-490f-9156-9d55c0f157c7
-- title:
--   Minkowski's first inequality in ℝⁿ, n ≥ 2, via the right derivative of vol(K + tM), with its equality case
-- statement:
--   Let $n \ge 2$ be a natural number and work in $\mathbb R^n$ as `EuclideanSpace ℝ (Fin n)`, with its volume $\mathrm{vol}$ (Mathlib's `volume`, Lebesgue measure) and $\mathrm{vol}(S)$ read as a real number (`volume.real S`, the measure converted to $\mathbb R$). Let $K, M \subseteq \mathbb R^n$ be compact convex sets with nonempty interior (`IsCompact`, `Convex ℝ`, `(interior _).Nonempty`). Let $d$ be a real number, and assume that the function $t \mapsto \mathrm{vol}(K + tM)$ of a real variable $t$ has derivative $d$ at $t = 0$ within $[0, \infty)$ (`HasDerivWithinAt (fun t : ℝ => volume.real (K + t • M)) d (Ici 0) 0`). Here $K + tM$ is the pointwise set `K + t • M`. Then:
--   1. $$n\,\bigl(\mathrm{vol}(K)^{1/n}\bigr)^{n-1}\,\mathrm{vol}(M)^{1/n} \;\le\; d;$$
--   2. if equality holds in 1, then $K$ and $M$ are homothetic: there are a point $z \in \mathbb R^n$ and a real number $c > 0$ with $K = \{z + c\,x : x \in M\}$ (in Lean, `K = (fun x => z + c • x) '' M`).
--
--   Here $t^{1/n}$ is the real power `t ^ ((n:ℝ)⁻¹)`, the outer power $n - 1$ is a natural-number power, and $n$ is cast to $\mathbb R$.
--
--   The existence of the one-sided derivative is a hypothesis of the statement.
--
--   Lean: `OAI.PettyProjection.minkowski_first_inequality_euclidean`. It uses only Mathlib. OpenAI's `minkowski_derivative_bound_equality` states the same over `Space n` (which is `EuclideanSpace ℝ (Fin n)`), with $\mathrm{vol}(S)^{1/n}$ written `volumeRoot S`. This statement unfolds both. Its proof is OpenAI's proof of that theorem, which now follows from this statement.
-- source:
--   H. Minkowski, Volumen und Oberfläche, Mathematische Annalen 57 (1903), 447–495 (the inequality and its equality case for convex bodies). Proof: OpenAI, Petty's projection-volume conjecture in dimensions at least four, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 088, commit adc7f12, Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/ProjectionBodies/Homothety.lean (OpenAI's theorem OAI.PettyProjection.minkowski_derivative_bound_equality, restated with its abbreviation volumeRoot unfolded)

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

theorem minkowski_first_inequality_euclidean {n : ℕ} (hn : 2 ≤ n)
    {K M : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hiK : (interior K).Nonempty) (hM : IsCompact M) (hcM : Convex ℝ M)
    (hiM : (interior M).Nonempty) {d : ℝ}
    (hd : HasDerivWithinAt (fun t : ℝ => volume.real (K + t • M)) d (Ici 0) 0) :
    (n:ℝ) * (volume.real K ^ ((n:ℝ)⁻¹)) ^ (n - 1) * volume.real M ^ ((n:ℝ)⁻¹) ≤ d ∧
      (d = (n:ℝ) * (volume.real K ^ ((n:ℝ)⁻¹)) ^ (n - 1) * volume.real M ^ ((n:ℝ)⁻¹) →
        ∃ z : EuclideanSpace ℝ (Fin n), ∃ c : ℝ, 0 < c ∧ K = (fun x => z + c • x) '' M) := by
  sorry

end PettyProjection
end

end OAI
end
