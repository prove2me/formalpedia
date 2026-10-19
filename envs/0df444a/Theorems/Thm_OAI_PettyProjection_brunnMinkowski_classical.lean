-- Prove2me | Theorems.Thm_OAI_PettyProjection_brunnMinkowski_classical
-- name    : OAI.PettyProjection.brunnMinkowski_classical
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:05:56.217168+00:00
-- url     : https://prove2.me/theorems/5aeddd9e-bb4c-4029-927a-3ac69bd32d08
-- title:
--   Brunn–Minkowski inequality vol(A+B)^(1/n) ≥ vol(A)^(1/n) + vol(B)^(1/n) for compact convex sets in a finite-dimensional real inner product space
-- statement:
--   Let $E$ be a finite-dimensional real inner product space (`NormedAddCommGroup E`, `InnerProductSpace ℝ E`, `FiniteDimensional ℝ E`; $E$ may live in any universe) of dimension $n = \dim_{\mathbb R} E$ (`Module.finrank ℝ E`), and assume $n \ge 1$. Give $E$ a measurable structure that is its Borel $\sigma$-algebra (`MeasurableSpace E`, `BorelSpace E`). Its volume $\mathrm{vol}$ is Mathlib's `volume` for an inner product space: the Haar measure that gives the parallelepiped spanned by an orthonormal basis volume $1$. Read $\mathrm{vol}(S)$ as a real number (`volume.real S`, the measure converted to $\mathbb R$).
--
--   Let $A, B \subseteq E$ be compact convex sets with nonempty interior (`IsCompact`, `Convex ℝ`, `(interior _).Nonempty`). Then
--   $$\mathrm{vol}(A)^{1/n} + \mathrm{vol}(B)^{1/n} \;\le\; \mathrm{vol}(A + B)^{1/n},$$
--   where $A + B = \{x + y : x \in A,\ y \in B\}$ is the Minkowski sum (pointwise `A + B`) and $t^{1/n}$ is the real power `t ^ ((Module.finrank ℝ E : ℝ)⁻¹)`.
--
--   Lean: `OAI.PettyProjection.brunnMinkowski_classical`. It uses only Mathlib. Its proof applies OpenAI's `brunnMinkowski_innerProduct` (the concavity form $a\,\mathrm{vol}(A)^{1/n} + b\,\mathrm{vol}(B)^{1/n} \le \mathrm{vol}(aA + bB)^{1/n}$ on $E$) with $a = b = 1/2$, then uses $\mathrm{vol}(\tfrac12 S) = 2^{-n}\mathrm{vol}(S)$.
-- source:
--   H. Brunn, Über Ovale und Eiflächen, Inaugural-Dissertation, München, 1887; H. Minkowski, Geometrie der Zahlen, Teubner, Leipzig, 1896 (the inequality for convex bodies). Proof: OpenAI, Petty's projection-volume conjecture in dimensions at least four, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 088, commit adc7f12, Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/ProjectionBodies/BrunnMinkowski.lean (derived from OpenAI's theorem OAI.PettyProjection.brunnMinkowski_innerProduct)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF

noncomputable section
open Set MeasureTheory
open scoped Pointwise
namespace PettyProjection

theorem brunnMinkowski_classical {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hE : 0 < Module.finrank ℝ E) {A B : Set E}
    (hA : IsCompact A) (hcA : Convex ℝ A) (hiA : (interior A).Nonempty)
    (hB : IsCompact B) (hcB : Convex ℝ B) (hiB : (interior B).Nonempty) :
    volume.real A ^ ((Module.finrank ℝ E : ℝ)⁻¹) + volume.real B ^ ((Module.finrank ℝ E : ℝ)⁻¹)
      ≤ volume.real (A + B) ^ ((Module.finrank ℝ E : ℝ)⁻¹) := by
  sorry

end PettyProjection
end

end OAI
end
