-- Prove2me | Theorems.Thm_OAI_HenonLaneEmden_WeakPDE_weak_newton_lower
-- name    : OAI.HenonLaneEmden.WeakPDE.weak_newton_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:37:31.106073+00:00
-- url     : https://prove2.me/theorems/6652dc90-400b-41e3-a078-ac809b89d4cc
-- title:
--   The Newtonian potential of the Laplacian of a nonnegative weak supersolution is bounded by the function: (n−2)|S^(n−1)| u ≥ ∫ |x−y|^(2−n) g(y) dy when −Δu = g ≥ 0
-- statement:
--   Let $E$ be a finite-dimensional real inner product space of dimension $n \ge 3$, with its Borel σ-algebra and the Lebesgue measure `volume` of its inner product structure. Write $|\mathbb S^{n-1}|$ for the total mass of the measure that `volume` induces on the unit sphere (`(volume : Measure E).toSphere univ`, the surface area of the unit sphere). Let $u, g : E \to \mathbb R$ satisfy:
--   - $u$ is continuous and nonnegative everywhere;
--   - $g$ is locally integrable, continuous on $E \setminus \{0\}$, and nonnegative everywhere;
--   - $-\Delta u = g$ in the sense of distributions: for every $C^2$ function $\varphi$ with compact support, $\int_E u\,\Delta\varphi = -\int_E g\,\varphi$ ($\Delta$ is Mathlib's `Laplacian.laplacian`).
--
--   Then for every $x \in E$,
--   $$\int_E \|x - y\|^{2-n}\, g(y)\, dy \;\le\; (n-2)\,|\mathbb S^{n-1}|\; u(x),$$
--   the integral taken as a lower Lebesgue integral of the nonnegative function (in $[0, \infty]$).
--
--   With the Newton kernel $K(z) = |z|^{2-n} / ((n-2)|\mathbb S^{n-1}|)$ this is $K * g \le u$: a nonnegative weak supersolution of Laplace's equation dominates the Newtonian potential of its Laplacian, as in the Riesz decomposition of superharmonic functions (F. Riesz, 1926–1930).
--
--   Lean: `OAI.HenonLaneEmden.WeakPDE.weak_newton_lower`, OpenAI's theorem of that name (in `lean/OAI/Analysis/HenonEmden/Mollification.lean`). The statement uses only Mathlib's definitions and imports no definitions bundle.
-- source:
--   classical potential theory (the comparison underlying the Riesz decomposition: F. Riesz, Sur les fonctions subharmoniques et leur rapport à la théorie du potentiel, Acta Math. 48 (1926), 329–343 and 54 (1930), 321–360); proof and Lean code: OpenAI, The Subcritical Hénon–Lane–Emden Conjecture, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 370; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Subcritical-Henon-Lane-Emden-Conjecture-September-24-2026/paper.pdf, Lemma 2.2, inequality (2.3); Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HenonEmden/Mollification.lean (declaration OAI.HenonLaneEmden.WeakPDE.weak_newton_lower)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2 uι uE3

section Mollification

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
noncomputable section

open scoped Convolution

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE3} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

lemma weak_newton_lower (hn : 3 ≤ Module.finrank ℝ E) {u g : E → ℝ}
    (hu : Continuous u) (hg : LocallyIntegrable g)
    (hgc : ContinuousOn g ({0}ᶜ : Set E)) (hp : ∀ x, 0 ≤ u x) (hgp : ∀ x, 0 ≤ g x)
    (heq : ∀ (φ : E → ℝ), ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∫ y, u y*Laplacian.laplacian φ y) = -(∫ y, g y*φ y)) (x : E) :
    (∫⁻ y : E, ENNReal.ofReal (‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y)) ≤
      ENNReal.ofReal (((Module.finrank ℝ E:ℝ)-2)*
        ((volume : Measure E).toSphere univ).toReal*u x) := by
  sorry
end HenonLaneEmden.WeakPDE

end
end Mollification

end OAI
end
