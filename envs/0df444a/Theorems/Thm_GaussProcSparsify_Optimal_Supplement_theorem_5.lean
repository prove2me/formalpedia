-- Prove2me | Theorems.Thm_GaussProcSparsify_Optimal_Supplement_theorem_5
-- name    : GaussProcSparsify.Optimal.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:25:42.630471+00:00
-- url     : https://prove2.me/theorems/575ddd87-1f0a-4c57-b9db-71fea7de2f01
-- title:
--   Theorem 5 — exact cube approximation lower bound
-- statement:
--   Let $r>0$ be any value such that the coordinate cube $C_n(r)=[-r,r]^n$ has standard Gaussian measure $1/2$, and let $P$ be any intersection of $m$ closed halfspaces. Then both conclusions hold:
--   $$\operatorname{dist}_G(P,C_n(r))\ge\frac12-\sqrt{\frac{m\ln2}{2n}}.$$
--   $$\operatorname{dist}_G(P,C_n(r))\le\varepsilon<\frac12\quad\Longrightarrow\quad m\ge\frac{2(1/2-\varepsilon)^2}{\ln2}\,n.$$
--   The cube's normalization excludes dimension zero. No containment or restriction on the halfspace normals is assumed. This companion theorem retains the literal constants in the paper's geometric lower bound.
--
--   Differences from the source:
--   - encoding: Euclidean R^n → EuclideanSpace ℝ (Fin n); reason: the fixed Euclidean coordinates, inner product and standard Gaussian law are preserved
--   - encoding: intersection of at most a prescribed number of halfspaces → a finite list of normals and thresholds, with the bound on its length; reason: lists enumerate every finite presentation and allow zero normals, repetitions, empty sets and the empty intersection
--   - encoding: P is an intersection of m halfspaces → P is the intersection constructed from an arbitrary list H, and m is its length; reason: quantifying over all presentations includes every source polyhedron, without minimality or irredundancy assumptions
-- source:
--   Shivam Nadimpalli, Optimal Sparsification of Gaussian Processes, STOC 2027 submission #163 (October 2026), Theorem 5, PDF p. 6 (printed p. 5), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/163.pdf

import Definitions.Def_GaussProcSparsify_Optimal_Supplement_Geometry

open MeasureTheory ProbabilityTheory

namespace GaussProcSparsify.Optimal.Supplement

/-- Theorem 5, PDF p. 6 (restatement p. 34). The normalization itself excludes n=0.
Both the exact distance estimate and its rearranged consequence are retained. -/
theorem theorem_5 (n : ℕ) (r : ℝ) (hr : 0 < r)
    (hcube : gaussian n (cube n r) = (1 / 2 : ENNReal)) (H : List (Vec n × ℝ)) :
    1 / 2 - Real.sqrt ((H.length : ℝ) * Real.log 2 / (2 * n)) ≤
      gaussianDistance (halfspaceIntersection H) (cube n r) ∧
    (∀ ε : ℝ, gaussianDistance (halfspaceIntersection H) (cube n r) ≤ ε → ε < 1 / 2 →
      (2 * (1 / 2 - ε) ^ 2 / Real.log 2) * n ≤ (H.length : ℝ)) := by sorry

end GaussProcSparsify.Optimal.Supplement
