-- Prove2me | Theorems.Thm_OAI_HenonLaneEmden_WeakPDE_harmonic_distribution_nonneg_constant
-- name    : OAI.HenonLaneEmden.WeakPDE.harmonic_distribution_nonneg_constant
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:37:31.421346+00:00
-- url     : https://prove2.me/theorems/4fffed4d-d80f-4b96-98b9-641422f3cd49
-- title:
--   Liouville's theorem for nonnegative harmonic distributions: a nonnegative locally integrable weakly harmonic function on a Euclidean space of dimension at least 2 is almost everywhere constant
-- statement:
--   Let $E$ be a finite-dimensional real inner product space of dimension $n \ge 2$, with its Borel σ-algebra and the Lebesgue measure `volume` of its inner product structure. Let $h : E \to \mathbb R$ be locally integrable (`LocallyIntegrable h`) and nonnegative everywhere. Suppose that $h$ is harmonic in the sense of distributions: for every $C^2$ function $\varphi : E \to \mathbb R$ with compact support,
--   $$\int_E h(y)\, \Delta\varphi(y)\, dy = 0,$$
--   where $\Delta$ is Mathlib's Laplacian (`Laplacian.laplacian`). Then there is a constant $c \ge 0$ with $h(x) = c$ for almost every $x \in E$.
--
--   $$h \ge 0,\ \ h \in L^1_{\mathrm{loc}}(E),\ \ \Delta h = 0 \text{ in distributions},\ \ \dim E \ge 2 \;\Longrightarrow\; h = c \ge 0 \text{ almost everywhere}.$$
--
--   This is the classical Liouville theorem for nonnegative harmonic functions, in distributional form: by Weyl's lemma a harmonic distribution is a harmonic function, and a nonnegative entire harmonic function is constant. In OpenAI's proof both steps go through mollification.
--
--   Lean: `OAI.HenonLaneEmden.WeakPDE.harmonic_distribution_nonneg_constant`, OpenAI's theorem of that name (in `lean/OAI/Analysis/HenonEmden/NewtonPotential.lean`). The statement uses only Mathlib's definitions and imports no definitions bundle.
-- source:
--   classical (Liouville's theorem for nonnegative harmonic functions, with Weyl's lemma: H. Weyl, The method of orthogonal projection in potential theory, Duke Math. J. 7 (1940), 411–444); proof and Lean code: OpenAI, The Subcritical Hénon–Lane–Emden Conjecture, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 370; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Subcritical-Henon-Lane-Emden-Conjecture-September-24-2026/paper.pdf, proof of Lemma 2.2; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HenonEmden/NewtonPotential.lean (declaration OAI.HenonLaneEmden.WeakPDE.harmonic_distribution_nonneg_constant)

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
variable {E : Type uE3} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

lemma harmonic_distribution_nonneg_constant (hn : 2 ≤ Module.finrank ℝ E) {h : E → ℝ}
    (hi : LocallyIntegrable h) (hp : ∀ x, 0 ≤ h x)
    (heq : ∀ (φ : E → ℝ), ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∫ y, h y*Laplacian.laplacian φ y) = 0) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᵐ x, h x = c := by
  sorry
end HenonLaneEmden.WeakPDE

end
end NewtonPotential

end OAI
end
