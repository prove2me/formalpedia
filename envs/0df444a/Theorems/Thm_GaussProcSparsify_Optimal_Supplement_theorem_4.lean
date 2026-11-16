-- Prove2me | Theorems.Thm_GaussProcSparsify_Optimal_Supplement_theorem_4
-- name    : GaussProcSparsify.Optimal.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:24:29.092504+00:00
-- url     : https://prove2.me/theorems/3582d88a-b5f6-41ea-9496-4fefadc43fb0
-- title:
--   Theorem 4 — approximation of bounded geometric width
-- statement:
--   There is a universal constant $C>0$ such that, for every dimension $n$, $r\ge1$, $0<\varepsilon<1/2$ and every set $K\subseteq\mathbb R^n$ of geometric width at most $r$, there is a finite intersection $L$ of $m$ halfspaces satisfying
--   $$m\le\exp\left(C\frac{\log(1/\varepsilon)(r+\sqrt{\log(1/\varepsilon)})^4}{\varepsilon^2}\right),\qquad\operatorname{dist}_G(K,L)\le\varepsilon.$$
--   Geometric width uses arbitrary unit normals and thresholds of either sign with magnitude at most $r$. The set may be unbounded, empty or the whole space. This companion theorem gives Gaussian approximation with a halfspace count independent of ambient dimension.
--
--   Differences from the source:
--   - encoding: Euclidean R^n → EuclideanSpace ℝ (Fin n); reason: the fixed Euclidean coordinates, inner product and standard Gaussian law are preserved
--   - encoding: universal constants in asymptotic notation → positive existential constants before all instance parameters; reason: spells out the uniformity of the source bounds without selecting a numerical constant
--   - encoding: intersection of at most a prescribed number of halfspaces → a finite list of normals and thresholds, with the bound on its length; reason: lists enumerate every finite presentation and allow zero normals, repetitions, empty sets and the empty intersection
--   - encoding: a convex K of geometric width at most r → the displayed halfspace representation with signed bounded thresholds; reason: the representation already implies convexity and closedness, so no extra convexity or measurability hypothesis is added
-- source:
--   Shivam Nadimpalli, Optimal Sparsification of Gaussian Processes, STOC 2027 submission #163 (October 2026), Theorem 4, PDF p. 5 (printed p. 4), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/163.pdf

import Definitions.Def_GaussProcSparsify_Optimal_Supplement_Geometry

open MeasureTheory ProbabilityTheory

namespace GaussProcSparsify.Optimal.Supplement

/-- Theorem 4, PDF p. 5 (restatement p. 28). Arbitrary signed thresholds. -/
theorem theorem_4 : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (r ε : ℝ) (K : Set (Vec n)), 1 ≤ r → 0 < ε → ε < 1 / 2 →
      HasGeometricWidth K r →
      ∃ H : List (Vec n × ℝ),
        (H.length : ℝ) ≤ Real.exp
          (C * Real.log (1 / ε) * (r + Real.sqrt (Real.log (1 / ε))) ^ 4 / ε ^ 2) ∧
        gaussianDistance K (halfspaceIntersection H) ≤ ε := by sorry

end GaussProcSparsify.Optimal.Supplement
