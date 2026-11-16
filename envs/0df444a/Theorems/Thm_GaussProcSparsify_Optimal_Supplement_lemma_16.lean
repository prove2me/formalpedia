-- Prove2me | Theorems.Thm_GaussProcSparsify_Optimal_Supplement_lemma_16
-- name    : GaussProcSparsify.Optimal.Supplement.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:23:52.997263+00:00
-- url     : https://prove2.me/theorems/945c027d-ba07-4b9b-a342-0a49533eb95a
-- title:
--   Lemma 16 — exact-width halfspace sparsification
-- statement:
--   There is a universal constant $C>0$ such that, for every $r\ge1$, $0<\varepsilon<1/2$ and every arbitrary $T\subseteq r^{-1}S^{n-1}$, let $K=\bigcap_{t\in T}\{x:\langle t,x\rangle\le1\}$. There is a finite halfspace intersection $L$ with
--   $$m\le\exp\left(C\frac{\log(1/\varepsilon)(r+\sqrt{\log(1/\varepsilon)})^4}{\varepsilon^2}\right),\qquad\operatorname{dist}_G(K,L)\le\varepsilon.$$
--   Empty or infinite $T$ is allowed. This exact-width support result retains the full logarithmic rate used for general geometric width.
--
--   Differences from the source:
--   - encoding: Euclidean R^n → EuclideanSpace ℝ (Fin n); reason: the fixed Euclidean coordinates, inner product and standard Gaussian law are preserved
--   - encoding: universal constants in asymptotic notation → positive existential constants before all instance parameters; reason: spells out the uniformity of the source bounds without selecting a numerical constant
--   - encoding: intersection of at most a prescribed number of halfspaces → a finite list of normals and thresholds, with the bound on its length; reason: lists enumerate every finite presentation and allow zero normals, repetitions, empty sets and the empty intersection
--   - encoding: T⊆(1/r)Sⁿ⁻¹ and the associated K → every t∈T has norm 1/r, with K substituted by its defining intersection; reason: r≥1 makes the sphere formulation equivalent, and K is constructed rather than independently quantified
-- source:
--   Shivam Nadimpalli, Optimal Sparsification of Gaussian Processes, STOC 2027 submission #163 (October 2026), Lemma 16, PDF p. 26 (printed p. 25), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/163.pdf

import Definitions.Def_GaussProcSparsify_Optimal_Supplement_Geometry

open MeasureTheory ProbabilityTheory

namespace GaussProcSparsify.Optimal.Supplement

/-- Lemma 16, PDF p. 26. No finiteness or nonemptiness condition on T. -/
theorem lemma_16 : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (r ε : ℝ) (T : Set (Vec n)), 1 ≤ r → 0 < ε → ε < 1 / 2 →
      (∀ t ∈ T, ‖t‖ = 1 / r) →
      ∃ H : List (Vec n × ℝ),
        (H.length : ℝ) ≤ Real.exp
          (C * Real.log (1 / ε) * (r + Real.sqrt (Real.log (1 / ε))) ^ 4 / ε ^ 2) ∧
        gaussianDistance {x | ∀ t ∈ T, inner ℝ t x ≤ 1}
          (halfspaceIntersection H) ≤ ε := by sorry

end GaussProcSparsify.Optimal.Supplement
