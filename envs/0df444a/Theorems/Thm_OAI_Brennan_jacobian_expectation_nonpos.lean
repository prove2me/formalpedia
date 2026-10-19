-- Prove2me | Theorems.Thm_OAI_Brennan_jacobian_expectation_nonpos
-- name    : OAI.Brennan.jacobian_expectation_nonpos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T20:27:05.858809+00:00
-- url     : https://prove2.me/theorems/c2994b4b-a308-4582-9e56-3fa310a93e8a
-- title:
--   Under a weighted affine law with exponent above 1, the expected normalized Jacobian at the base point is nonpositive (OpenAI Brennan)
-- statement:
--   **Setting.** `DiskClass` is the compact class of normalized univalent disk maps: continuous functions $g$ on the unit disk whose extension by zero is holomorphic and injective on the disk with $g(0) = 0$ and $g'(0) = 1$ (`diskSchlichtSet`). For $g$ in the class, $F = $ `classFun g` is its half-plane model, $F(z) = 2i\,g\bigl((z-i)/(z+i)\bigr)$. Points of the upper half-plane are $z = x + iy$, $y > 0$ (`halfPlane`).
--
--   For such $z$, `rerootClass g z` is the member of the class whose half-plane model is $w \mapsto \bigl(F(x + yw) - F(z)\bigr)/\bigl(y\,F'(z)\bigr)$, and `classWeight g z` $= |1/F'(z)|^2$. For a probability measure $P$ on `DiskClass` and real $\beta$, the condition `HasWeightedLaw P β` says: for every $z$ in the upper half-plane and every measurable $\Phi : $ `DiskClass` $\to [0, \infty]$,
--   $$\int |1/F'(z)|^2\;\Phi(\texttt{rerootClass}\ g\ z)\;dP(g) = y^{-\beta}\int\Phi\,dP,$$
--   as lower Lebesgue integrals ($y^{-\beta}$ the real power).
--
--   For $f : \mathbb C \to \mathbb C$ and real $k$, the critical map is $G(z) = f(z) - (i/k)\,y\,f'(z)$ (`criticalMap f k`), and the normalized Jacobian `normalizedJacobian f k z` is the determinant of the real derivative of $G$ at $z$, divided by $|f'(z)|^2$.
--
--   **Statement.** Let $P$ be a probability measure on `DiskClass` and $\beta > 1$ a real number with `HasWeightedLaw P β`. Then
--   $$\int \texttt{normalizedJacobian}\bigl(\texttt{classFun}\ g,\ (\beta + 3)/4,\ i\bigr)\;dP(g) \;\le\; 0.$$
--
--   This is the conclusion $\mathbb E J_F(i) \le 0$ of the paper's Section 6 (transport between saddles and maxima). Lean: `OAI.Brennan.jacobian_expectation_nonpos`, OpenAI's lemma of that name (in `lean/OAI/Analysis/IntegralMeans/Moments.lean`). The definitions come from the published bundle `Def_Brennan` and the definitions bundle `OAIQWBRN000` of this split. The statement keeps OpenAI's local `irreducible` attributes for four of those definitions, which only control unfolding.
-- source:
--   OpenAI, Brennan's conjecture and sharp inverse-square integral means, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 072; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Brennans-conjecture-and-sharp-inverse-square-integral-means-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/IntegralMeans/Moments.lean (declaration OAI.Brennan.jacobian_expectation_nonpos)

import Mathlib
import Definitions.Def_Brennan
import Definitions.Def_OAIQWBRN000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun
attribute [local irreducible] rerootClass
attribute [local irreducible] inverseDensity inverseJacDensity

lemma jacobian_expectation_nonpos (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : HasWeightedLaw P β) (hβ : 1 < β) :
    (∫ g, normalizedJacobian (classFun g) ((β+3)/4) Complex.I ∂(P : Measure DiskClass)) ≤ 0 := by
  sorry

end Brennan

end

end OAI
end
