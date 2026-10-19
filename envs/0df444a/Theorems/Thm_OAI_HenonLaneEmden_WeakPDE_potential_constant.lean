-- Prove2me | Theorems.Thm_OAI_HenonLaneEmden_WeakPDE_potential_constant
-- name    : OAI.HenonLaneEmden.WeakPDE.potential_constant
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:37:30.958845+00:00
-- url     : https://prove2.me/theorems/246701f4-db60-4a96-be8d-58b29087409e
-- title:
--   Riesz decomposition on Euclidean space: a weak solution of −Δu = g ≥ 0 that dominates the Newtonian potential of g equals that potential plus a nonnegative constant
-- statement:
--   Let $E$ be a finite-dimensional real inner product space of dimension $n \ge 3$, with its Borel σ-algebra and the Lebesgue measure `volume` of its inner product structure. Write $|\mathbb S^{n-1}|$ for the total mass of the measure that `volume` induces on the unit sphere (`(volume : Measure E).toSphere univ`, the surface area of the unit sphere), and
--   $$P(x) = \int_E \|x - y\|^{2-n}\, g(y)\, dy$$
--   (a Bochner integral). Let $u, g : E \to \mathbb R$ satisfy:
--   - $u$ is continuous; $g$ is measurable and nonnegative everywhere;
--   - for every $x$, the function $y \mapsto \|x-y\|^{2-n} g(y)$ is integrable;
--   - $P(x) \le (n-2)\,|\mathbb S^{n-1}|\, u(x)$ for every $x$;
--   - $-\Delta u = g$ in the sense of distributions: for every $C^2$ function $\varphi$ with compact support, $\int_E u\,\Delta\varphi = -\int_E g\,\varphi$ ($\Delta$ is Mathlib's `Laplacian.laplacian`).
--
--   Then there is a constant $c \ge 0$ with
--   $$(n-2)\,|\mathbb S^{n-1}|\; u(x) \;=\; P(x) + c \qquad \text{for almost every } x \in E.$$
--
--   With the Newton kernel $K(z) = |z|^{2-n}/((n-2)|\mathbb S^{n-1}|)$ this says $u = K * g + c'$ almost everywhere with $c' \ge 0$: the Riesz decomposition of a superharmonic function on $\mathbb R^n$ into a Newtonian potential and a harmonic part (F. Riesz, 1926–1930), where the harmonic part, nonnegative by the third hypothesis, is constant by Liouville's theorem.
--
--   Lean: `OAI.HenonLaneEmden.WeakPDE.potential_constant`. This is OpenAI's theorem of that name (in `lean/OAI/Analysis/HenonEmden/NewtonPotential.lean`) with OpenAI's `rawPotential g x` written out as the integral $P(x)$, so the statement uses only Mathlib's definitions and imports no definitions bundle.
-- source:
--   F. Riesz, Sur les fonctions subharmoniques et leur rapport à la théorie du potentiel, Acta Math. 48 (1926), 329–343 and 54 (1930), 321–360 (the decomposition); proof and Lean code: OpenAI, The Subcritical Hénon–Lane–Emden Conjecture, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 370; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Subcritical-Henon-Lane-Emden-Conjecture-September-24-2026/paper.pdf, Lemma 2.2, identity (2.4); Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HenonEmden/NewtonPotential.lean (declaration OAI.HenonLaneEmden.WeakPDE.potential_constant)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2 uE3 uE4

section NewtonPotential

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open Set Filter Topology MeasureTheory
open Set Filter Topology
open MeasureTheory
open scoped Convolution
open Set Filter Topology
open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE4} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

lemma potential_constant (hn : 3 ≤ Module.finrank ℝ E) {u g : E → ℝ}
    (hu : Continuous u) (hg : Measurable g) (hgp : ∀ x, 0 ≤ g x)
    (hki : ∀ x, Integrable (fun y => ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y))
    (hlower : ∀ x, (∫ y, ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y) ≤ ((Module.finrank ℝ E:ℝ)-2)*
      ((volume : Measure E).toSphere univ).toReal*u x)
    (heq : ∀ (φ : E → ℝ), ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∫ y, u y*Laplacian.laplacian φ y) = -(∫ y, g y*φ y)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᵐ x, ((Module.finrank ℝ E:ℝ)-2)*
      ((volume : Measure E).toSphere univ).toReal*u x =
        (∫ y, ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y)+c := by
  sorry

end HenonLaneEmden.WeakPDE

end
end NewtonPotential

end OAI
end
